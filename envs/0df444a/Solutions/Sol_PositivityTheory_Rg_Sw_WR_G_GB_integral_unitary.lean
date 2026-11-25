-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GB.integral_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:58.297642+00:00
-- url     : https://prove2.me/submissions/10678665-952c-4805-94cb-8385b53cdd89

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBaseA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBaseB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GB_normSq_det_unitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G PositivityTheory.Rg.Sw.WR.G.GB
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.G.GB
theorem _root_.solution (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℂ) : ∫ r, g (U *ᵥ r) = ∫ r, g r := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  let eC : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
    LinearEquiv.ofLinear (Matrix.toLin' U) (Matrix.toLin' (star U))
      (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  let eR : (Fin n → ℂ) ≃ₗ[ℝ] (Fin n → ℂ) := eC.restrictScalars ℝ
  let e : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ) := eR.toContinuousLinearEquiv
  let me : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) := e.toHomeomorph.toMeasurableEquiv
  have hcoe : ∀ r, me r = U *ᵥ r := fun r => by
    simp [me, e, eR, eC, Matrix.toLin'_apply]
  have hdet : LinearMap.det ((eC : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars]
    have : (eC : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = Matrix.toLin' U := rfl
    rw [this, LinearMap.det_toLin', Algebra.norm_complex_apply, normSq_det_unitary U hU]
  have hmap : Measure.map (((eC : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ)) volume =
      (volume : Measure (Fin n → ℂ)) := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  have hpres : MeasurePreserving me volume volume := by
    refine ⟨me.measurable, ?_⟩
    have : (me : (Fin n → ℂ) → (Fin n → ℂ)) =
        (((eC : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ) : (Fin n → ℂ) → (Fin n → ℂ)) := by
      funext r; rw [hcoe r]; simp [eC, Matrix.toLin'_apply]
    rw [this, hmap]
  have := hpres.integral_comp' g
  simpa [hcoe] using this
end PositivityTheory.Rg.Sw.WR.G.GB
