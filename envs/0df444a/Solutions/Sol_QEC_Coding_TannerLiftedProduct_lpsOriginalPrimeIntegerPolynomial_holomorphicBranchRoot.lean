-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_holomorphicBranchRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:06:40.611818+00:00
-- url     : https://prove2.me/submissions/36c3554a-9394-4a1a-a5a4-9b4ac1e4d111

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchHolomorphic_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_branchRoot
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJHolomorphicEvalQ_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (i : Option (Fin p)) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).eval₂
      lpsOriginalJHolomorphicEvalZ (lpsOriginalPrimeBranchHolomorphic p i)=0 := by
  apply Subtype.ext
  funext τ
  let e : LPSOriginalHolomorphicRing →+* ℂ :=
    { toFun f := f.val τ
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hc : e.comp lpsOriginalJHolomorphicEvalZ=
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) := by
    apply RingHom.ext
    intro P
    change (lpsOriginalJHolomorphicEvalQ (P.map (algebraMap ℤ ℚ))).val τ=
      (P.map (Int.castRingHom ℂ)).eval (lpsOriginalJInvariant τ)
    rw [lpsOriginalJHolomorphicEvalQ_apply,Polynomial.eval_map,Polynomial.eval₂_map]
    congr 1
  have h := Polynomial.hom_eval₂ (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos)
    lpsOriginalJHolomorphicEvalZ e (lpsOriginalPrimeBranchHolomorphic p i)
  rw [hc] at h
  have hb : e (lpsOriginalPrimeBranchHolomorphic p i)=lpsOriginalPrimeBranch p i τ :=
    lpsOriginalPrimeBranchHolomorphic_apply p i τ
  rw [hb] at h
  exact h.trans (lpsOriginalPrimeIntegerPolynomial_branchRoot p i τ)
end QEC.Coding.TannerLiftedProduct
