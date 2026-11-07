-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_pointwiseProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:31:31.251209+00:00
-- url     : https://prove2.me/submissions/a217adac-ca57-4be1-b5f5-c63254a546ce

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeBranchHolomorphic_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_holomorphicProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJHolomorphicEvalQ_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (τ : ℍ) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ)))=
      ∏ i : Option (Fin p), (Polynomial.X-Polynomial.C (lpsOriginalPrimeBranch p i τ)) := by
  classical
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
  have h:=congrArg (Polynomial.map e) (lpsOriginalPrimeIntegerPolynomial_holomorphicProduct p)
  rw [Polynomial.map_map,hc,Polynomial.map_prod] at h
  convert h using 1
  apply Finset.prod_congr rfl
  intro i _
  rw [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
  have hb : e (lpsOriginalPrimeBranchHolomorphic p i)=lpsOriginalPrimeBranch p i τ :=
    lpsOriginalPrimeBranchHolomorphic_apply p i τ
  rw [hb]
end QEC.Coding.TannerLiftedProduct
