-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.conjugation_invariant_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:24.159226+00:00
-- url     : https://prove2.me/submissions/e8c8f1dc-cb74-4651-a922-45adedf95c19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HaarSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ModOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstLeftInvMuInf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_Development
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_haarOn_of
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_haarOn_unique
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_genModOne_of
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_generic_haar_subgroup
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_instConj_of
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_isClosed_Ninf
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_measure_subFacts
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_place_decomposition_instance


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory NumberField
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution : ConjInv := by
  intro I r e f z hF μ hμ h hh
  have hN : IsClosed ((PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z : Subgroup I.Ginf) : Set I.Ginf) :=
    PI.ScMuExists.UnitaryGroupMassFormula.isClosed_Ninf (I := I) (e := e) (z := z)
  have hC := PI.ScMuExists.UnitaryGroupMassFormula.instConj_of
    (PI.ScMuExists.UnitaryGroupMassFormula.genModOne_of PI.ScMuExists.UnitaryGroupMassFormula.generic_haar_subgroup)
    PI.ScMuExists.UnitaryGroupMassFormula.place_decomposition_instance PI.ScMuExists.UnitaryGroupMassFormula.measure_subFacts
  have hconj := hC I r e f z hF (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z)
    (PI.ScMuExists.UnitaryGroupMassFormula.HSub I (PI.ScMuExists.UnitaryGroupMassFormula.frameSet I e f z)) hN rfl rfl h hh
  have hG := PI.ScMuExists.UnitaryGroupMassFormula.generic_haar_subgroup I.Ginf (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z) hN
  have hν : HaarOn (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z) (PI.ScMuExists.UnitaryGroupMassFormula.haarSub _ hN) :=
    ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1⟩
  obtain ⟨c, -, -, hc⟩ := haarOn_unique (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z) hN hν (haarOn_of I e z μ hμ)
  rw [hc, Measure.map_smul, hconj]
end PI.NMeasInv.UnitaryGroupMassFormula
