-- Prove2me | solution 1 for PI.RhsWLim.W.RI.descUniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:46.204394+00:00
-- url     : https://prove2.me/submissions/cbef196c-4e0d-4f24-a50c-361b087726e0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvDA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvD
import Theorems.Thm_PI_RhsWLim_W_RI_continuous_orbV_inc
import Theorems.Thm_PI_RhsWLim_W_RI_stabH_closed
import Theorems.Thm_PI_RhsWLim_W_RI_jH_memb
import Theorems.Thm_PI_RhsWLim_W_RI_map_jH
import Theorems.Thm_PI_RhsWLim_W_RI_nuH_left
import Theorems.Thm_PI_RhsWLim_W_RI_pull_right
import Theorems.Thm_PI_RhsWLim_W_RI_orb_fib
import Theorems.Thm_PI_RhsWLim_W_HU_inc_memb
import Theorems.Thm_PI_RhsWLim_W_HU_map_pull
import Theorems.Thm_PI_RhsWLim_W_HU_pull_sigmaFinite
import Theorems.Thm_PI_RhsWLim_W_RI_desc_uniq
import Theorems.Thm_PI_RhsWLim_W_RI_orbV_cont


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
open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W
variable {k r : ℕ}
namespace PI.RhsWLim.W.RI
theorem _root_.solution : DescUniq := by
  intro k r z' μW' hW hfin ν₁ ν₂ hσ₁ hσ₂ hc₁ hc₂ hr₁ hr₂ hm
  have : SigmaFinite μW' := hW.1
  have hl := nuH_left hW
  have hmass : (μW'.comap (jH z')) univ = μW' univ := by
    conv_rhs => rw [← map_jH hW]
    rw [Measure.map_apply (jH_memb z').measurable MeasurableSet.univ, preimage_univ]
  have h0 : (μW'.comap (jH z')) univ ≠ 0 := by
    rw [hmass]
    exact fun h => hW.2.1 (Measure.measure_univ_eq_zero.1 h)
  have hf : (μW'.comap (jH z')) univ ≠ ⊤ := by rw [hmass]; exact hfin
  have : SigmaFinite (HU.pull ν₁) := HU.pull_sigmaFinite ν₁
  have : SigmaFinite (HU.pull ν₂) := HU.pull_sigmaFinite ν₂
  have hpm : ∀ ν : Measure (Mt k r), ν {x | Matrix.of x ∉ UWb k r} = 0 →
      (HU.pull ν).map (fun g => orbV k r z' (HU.inc g)) = ν.map (orbV k r z') := by
    intro ν hc
    have e : (fun g : HU.Gp k r => orbV k r z' (HU.inc g)) = orbV k r z' ∘ HU.inc := rfl
    rw [e, ← Measure.map_map (orbV_cont z').measurable HU.inc_memb.measurable, HU.map_pull ν hc]
  have key := desc_uniq (stabH k r z') (stabH_closed z') (μW'.comap (jH z')) h0 hf
    (fun g => orbV k r z' (HU.inc g)) (continuous_orbV_inc z') (orb_fib z') (HU.pull ν₁) (HU.pull ν₂)
    (pull_right ν₁ hc₁ hr₁) (pull_right ν₂ hc₂ hr₂) (by rw [hpm ν₁ hc₁, hpm ν₂ hc₂, hm])
  rw [← HU.map_pull ν₁ hc₁, ← HU.map_pull ν₂ hc₂, key]
end PI.RhsWLim.W.RI
