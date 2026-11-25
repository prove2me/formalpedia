-- Prove2me | solution 1 for PI.RhsWLim.W.RI.nuH_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:29:41.749986+00:00
-- url     : https://prove2.me/submissions/4537a044-e90f-4631-ba93-faf72f262e0f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvDA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvD
import Theorems.Thm_PI_RhsWLim_W_RI_jH_memb
import Theorems.Thm_PI_RhsWLim_W_RI_jH_mem
import Theorems.Thm_PI_RhsWLim_W_RI_map_jH
import Theorems.Thm_PI_RhsWLim_W_HU_lmulM_cont


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
theorem _root_.solution {z' : Fin (2 * r + k + 1) → ℂ} {μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z') μW') :
    (μW'.comap (jH z')).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  have hg : Measurable (fun h : stabH k r z' => g * h) := (continuous_const_mul g).measurable
  have e : (jH z' ∘ fun h : stabH k r z' => g * h) = lmulM (Matrix.of (jH z' g)) ∘ jH z' := funext fun h => rfl
  calc (μW'.comap (jH z')).map (fun h => g * h)
      = (((μW'.comap (jH z')).map (fun h => g * h)).map (jH z')).comap (jH z') := ((jH_memb z').comap_map _).symm
    _ = (((μW'.comap (jH z')).map (jH z')).map (lmulM (Matrix.of (jH z' g)))).comap (jH z') := by
        rw [Measure.map_map (jH_memb z').measurable hg, e,
          ← Measure.map_map (HU.lmulM_cont _).measurable (jH_memb z').measurable]
    _ = ((μW'.comap (jH z')).map (jH z')).comap (jH z') := by
        rw [map_jH hW, hW.2.2.2 _ (jH_mem z' g)]
    _ = μW'.comap (jH z') := (jH_memb z').comap_map _
end PI.RhsWLim.W.RI
