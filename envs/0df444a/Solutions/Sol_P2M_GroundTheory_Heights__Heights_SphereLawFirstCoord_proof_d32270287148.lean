-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_proof_d32270287148
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:08:39.120938+00:00
-- url     : https://prove2.me/submissions/79960c3e-748d-4747-b665-6993086ec270

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawFirstCoord
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_density_Ici_1e097aef9654
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_law_Ici_f045ceeff4d1

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
open MeasureTheory ProbabilityTheory Set Real
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SphereLawFirstCoord
theorem _root_.solution : SphereLawFirstCoord.Statement := by
  intro N hN
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  show (sphereLaw (k + 1 + 1)).map (fun z ↦ ‖z 0‖ ^ 2) = _
  have hd : (fun x : ℝ ↦ ENNReal.ofReal (Set.indicator (Set.Icc 0 1)
      (fun x ↦ ((k + 1 + 1 : ℕ) - 1 : ℝ) * (1 - x) ^ (k + 1 + 1 - 2)) x)) =
      fun x ↦ ENNReal.ofReal (Set.indicator (Set.Icc 0 1) (fun x ↦ (k + 1 : ℝ) * (1 - x) ^ k) x) := by
    have h2 : k + 1 + 1 - 2 = k := by omega
    simp only [h2]
    push_cast
    ring_nf
  rw [hd]
  have := (sphereLaw (k + 1 + 1)).isFiniteMeasure_map fun z : Fin (k + 1 + 1) → ℂ ↦ ‖z 0‖ ^ 2
  refine Measure.ext_of_Ici _ _ fun c ↦ ?_
  rw [SphereLawFirstCoord.law_Ici, SphereLawFirstCoord.density_Ici]
end SphereLawFirstCoord
end GroundTheory.Heights₂.Heights
