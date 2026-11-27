-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeDeepWeightMass_proof_a50cf3ffc838
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:08:43.643168+00:00
-- url     : https://prove2.me/submissions/c11811d9-a18e-42b9-abad-4a2d57c5fca8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepWeightMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepWeightMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_measurable_poincareDeepWeight__a1ff6f0b8f45
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_lintegral_poincareDeepWeight_lt_top_ad8ff22c8214

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace TubeDeepWeightMass
theorem _root_.solution : TubeDeepWeightMass.Statement := by
  intro d R
  set T : Set (Fin d → ℂ) := {w | ∀ i, ‖w i‖ ≤ R} with hTdef
  have hT : volume T < ⊤ := by
    have hsub : T ⊆ Metric.closedBall (0 : Fin d → ℂ) |R| := by
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg (abs_nonneg R)).2 fun i => (hw i).trans (le_abs_self R)
    exact (measure_mono hsub).trans_lt measure_closedBall_lt_top
  have e := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0
  have hpre : {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R} =
      MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0 ⁻¹' (Set.univ ×ˢ T) := by
    ext z
    simp [hTdef, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.tail]
  have key := e.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _)
    (fun p : ℂ × (Fin d → ℂ) => ENNReal.ofReal (poincareDeepWeight p.1) * (fun _ => (1 : ENNReal)) p.2)
    (Set.univ ×ˢ T)
  rw [hpre]
  simp only [mul_one] at key
  have h0 : ∀ z : Fin (d + 1) → ℂ, (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0 z).1 = z 0 := fun z => rfl
  simp only [h0] at key
  rw [key, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have := lintegral_prod_mul (μ := (volume : Measure ℂ).restrict Set.univ)
    (ν := (volume : Measure (Fin d → ℂ)).restrict T)
    (ENNReal.measurable_ofReal.comp measurable_poincareDeepWeight').aemeasurable
    (aemeasurable_const (b := (1 : ENNReal)))
  simp only [mul_one, Function.comp_apply] at this
  rw [this, Measure.restrict_univ, setLIntegral_one]
  exact ENNReal.mul_lt_top lintegral_poincareDeepWeight_lt_top hT
end TubeDeepWeightMass
end GroundTheory.Heights₂.Heights
