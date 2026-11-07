-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalRelation_pointwiseProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:57:29.612636+00:00
-- url     : https://prove2.me/submissions/1f6a53a9-d201-4d49-bd47-ee3d5143c3d5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalRelation_holomorphicProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJHolomorphicEvalQ_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (Φ : Polynomial (Polynomial ℚ))
    (hΦ : Φ.Monic)
    (hdeg : Φ.natDegree=Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))
    (hroot : ∀ τ : ℍ,
      Φ.eval₂ ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ)=0)
    (τ : ℍ) :
    letI := Fintype.ofFinite (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
    Φ.map ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ)))=
      ∏ x : (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
        (Polynomial.X-Polynomial.C (lpsOriginalJDilated N hN (x.out.val⁻¹•τ))) := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  let e : LPSOriginalHolomorphicRing →+* ℂ :=
    { toFun f := f.val τ
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hc : e.comp lpsOriginalJHolomorphicEvalQ=
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ))) := by
    apply RingHom.ext
    intro P
    change (lpsOriginalJHolomorphicEvalQ P).val τ=
      (P.map (algebraMap ℚ ℂ)).eval (lpsOriginalJInvariant τ)
    rw [Polynomial.eval_map]
    exact lpsOriginalJHolomorphicEvalQ_apply P τ
  have h := congrArg (Polynomial.map e)
    (lpsOriginalRationalRelation_holomorphicProduct N hN Φ hΦ hdeg hroot)
  rw [Polynomial.map_map,hc,Polynomial.map_prod] at h
  convert h using 1
  apply Finset.prod_congr rfl
  intro x _hx
  rw [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
  rfl
end QEC.Coding.TannerLiftedProduct
