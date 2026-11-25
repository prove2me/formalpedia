-- Prove2me | solution 1 for PI.RhsWLim.W.gauge_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:33:29.867799+00:00
-- url     : https://prove2.me/submissions/dbf29a7b-ee8c-4c52-82ee-a9a282b309f0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_UnimodS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim HU
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (ν : Measure (Mt k r)) (hG : IsGaugeOn k r (UWb k r) ν) :
    ∃ ρ : ℝ, 0 < ν (bBall k r ρ) ∧ ν (bBall k r ρ) < ⊤ := by
  have h := hG.2.eventually_const_lt (show (0 : ℝ) < 1 from one_pos)
  obtain ⟨ρ, hρ⟩ := h.exists
  refine ⟨ρ, ?_, ?_⟩
  · rcases eq_or_ne (ν (bBall k r ρ)) 0 with h0 | h0
    · exfalso
      have : (ν (expBall (k := k) (r := r) (UWb k r) ρ)).toReal = 0 := by
        show (ν (bBall k r ρ)).toReal = 0
        rw [h0]; rfl
      rw [this, zero_div] at hρ; exact lt_irrefl _ hρ
    · exact pos_iff_ne_zero.2 h0
  · rcases eq_or_ne (ν (bBall k r ρ)) ⊤ with h0 | h0
    · exfalso
      have : (ν (expBall (k := k) (r := r) (UWb k r) ρ)).toReal = 0 := by
        show (ν (bBall k r ρ)).toReal = 0
        rw [h0]; rfl
      rw [this, zero_div] at hρ; exact lt_irrefl _ hρ
    · exact lt_top_iff_ne_top.2 h0
end PI.RhsWLim.W
