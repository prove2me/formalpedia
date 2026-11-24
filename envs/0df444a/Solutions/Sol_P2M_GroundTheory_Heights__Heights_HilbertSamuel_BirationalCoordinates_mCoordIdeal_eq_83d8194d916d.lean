-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_mCoordIdeal_eq_83d8194d916d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:16.663693+00:00
-- url     : https://prove2.me/submissions/c5f13725-9844-4f54-a4fe-abc9090b2f0b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsBirationalCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinatesA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
variable {κ : Type} [Fintype κ] {Ω Ω'' : Type} [Field Ω] [Field Ω'']
  (j : Ω'' →+* Ω) {μ : Ω} (hμ : μ ≠ 0) {x : Ix κ → Ω} {y : Ix κ → Ω''} (hx : ∀ p, x p = μ * j (y p))
include hμ hx
omit [Fintype κ]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
theorem _root_.solution : mCoordIdeal (ι := GlobalTheory κ) y = mCoordIdeal (ι := GlobalTheory κ) x := by
  let φ : MvPolynomial Unit Ω →ₐ[Ω] MvPolynomial Unit Ω := aeval fun k => C μ * X k
  let ψ : MvPolynomial Unit Ω →ₐ[Ω] MvPolynomial Unit Ω := aeval fun k => C μ⁻¹ * X k
  have hψφ : ∀ q, ψ (φ q) = q := by
    have h : ψ.comp φ = AlgHom.id Ω _ := by
      refine MvPolynomial.algHom_ext fun k => ?_
      simp only [AlgHom.comp_apply, AlgHom.id_apply, φ, ψ, aeval_X, map_mul, algHom_C, algebraMap_eq]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hμ, C_1, one_mul]
    intro q
    exact AlgHom.congr_fun h q
  have hcomp : (mConeMap (ι := GlobalTheory κ) x).toRingHom =
      (φ.toRingHom.comp (MvPolynomial.map j)).comp (mConeMap (ι := GlobalTheory κ) y).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun n => by simp) (fun p => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      mConeMap, aeval_X, map_mul, map_C, map_X, φ, algHom_C, algebraMap_eq, hx p, ]
    ring
  ext f
  simp only [mCoordIdeal, RingHom.mem_ker]
  have hf : mConeMap (ι := GlobalTheory κ) x f = φ (MvPolynomial.map j (mConeMap (ι := GlobalTheory κ) y f)) :=
    congrArg (fun F : MRing (GlobalTheory κ) →+* MvPolynomial Unit Ω => F f) hcomp
  rw [hf]
  constructor
  · intro h
    rw [h, map_zero, map_zero]
  · intro h
    have h1 : MvPolynomial.map j (mConeMap (ι := GlobalTheory κ) y f) = 0 := by
      rw [← hψφ (MvPolynomial.map j _), h, map_zero]
    exact MvPolynomial.map_injective j j.injective (by rw [h1, map_zero])
end GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
