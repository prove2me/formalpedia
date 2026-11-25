-- Prove2me | solution 1 for PI.RhsWLim.W.gauge_of_lim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:15:17.015607+00:00
-- url     : https://prove2.me/submissions/af9fec9f-133e-43a4-8d23-eb1f001a3a77

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
namespace PI.RhsWLim.W
theorem _root_.solution {k r : ℕ} (νg : Measure (Mt k r)) (hH : IsHaarOn (UWb k r) νg)
    (hL : ∀ m ∈ UWb k r, Tendsto (fun ρ : ℝ => (νg (tBall k r m ρ)).toReal / bVol k r ρ) (𝓝[>] 0) (𝓝 1)) :
    IsGaugeOn k r (UWb k r) νg := by
  refine ⟨hH, ?_⟩
  have h1 : (1 : Mat k r) ∈ UWb k r := by
    refine ⟨?_, fun a => ⟨?_, ?_⟩⟩ <;> simp [UH]
  have e : ∀ ρ, tBall k r 1 ρ = expBall (k := k) (r := r) (UWb k r) ρ := fun ρ => by
    ext x
    simp [tBall, bBall]
  have h2 := hL 1 h1
  simp only [e] at h2
  exact h2
end PI.RhsWLim.W
