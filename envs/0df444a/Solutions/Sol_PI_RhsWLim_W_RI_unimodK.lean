-- Prove2me | solution 1 for PI.RhsWLim.W.RI.unimodK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:38:53.839665+00:00
-- url     : https://prove2.me/submissions/8d32bcf8-24df-44a1-9867-943fda722c00

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvU
import Theorems.Thm_PI_RhsWLim_W_RI_fin_right
import Theorems.Thm_PI_RhsWLim_W_RI_jH_memb
import Theorems.Thm_PI_RhsWLim_W_RI_map_jH
import Theorems.Thm_PI_RhsWLim_W_RI_nuH_left
import Theorems.Thm_PI_RhsWLim_W_RI_rmulM_cont


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
namespace PI.RhsWLim.W.RI
theorem _root_.solution : UnimodK := by
  intro k r z μ hW hfin b hb
  have : SigmaFinite μ := hW.1
  have hl := nuH_left hW
  have hmass : (μ.comap (jH z)) univ = μ univ := by
    conv_rhs => rw [← map_jH hW]
    rw [Measure.map_apply (jH_memb z).measurable MeasurableSet.univ, preimage_univ]
  have : IsFiniteMeasure (μ.comap (jH z)) := ⟨by rw [hmass]; exact lt_top_iff_ne_top.2 hfin⟩
  have h0 : μ.comap (jH z) ≠ 0 := by
    intro h
    apply hW.2.1
    rw [← map_jH hW, h, Measure.map_zero]
  have : SecondCountableTopology (stabH k r z) :=
    inferInstanceAs (SecondCountableTopology ((stabH k r z : Set (HU.Gp k r))))
  have : BorelSpace (stabH k r z) := inferInstanceAs (BorelSpace ((stabH k r z : Set (HU.Gp k r))))
  let g : stabH k r z := ⟨⟨fun i j => b i j, ⟨hb.1, hb.2.1⟩⟩, hb.2.2⟩
  have hR := fin_right (μ.comap (jH z)) h0 g
  have e : rmulM b ∘ jH z = jH z ∘ (· * g) := funext fun x => rfl
  calc μ.map (rmulM b) = ((μ.comap (jH z)).map (jH z)).map (rmulM b) := by rw [map_jH hW]
    _ = ((μ.comap (jH z)).map (· * g)).map (jH z) := by
        rw [Measure.map_map (rmulM_cont b).measurable (jH_memb z).measurable, e,
          ← Measure.map_map (jH_memb z).measurable (measurable_mul_const g)]
    _ = μ := by rw [hR, map_jH hW]
end PI.RhsWLim.W.RI
