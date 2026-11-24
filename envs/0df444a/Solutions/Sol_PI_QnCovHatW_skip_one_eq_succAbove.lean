-- Prove2me | solution 1 for PI.QnCovHatW.skip_one_eq_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:11:46.425729+00:00
-- url     : https://prove2.me/submissions/6ee47ea2-021d-42a6-883a-5c18884e0814

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_InjDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_SkipOneEqSuccAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix Formalism.REAL Formalism.FourierDecayAlt.Q
open PI PI.QnCovHatW
namespace PI.QnCovHatW
theorem _root_.solution {m : ℕ} (i : Fin (m + 1)) (j : Fin m) : skip1 (t := m + 1) i j = i.succAbove j := by
  apply Fin.ext
  unfold skip1
  by_cases h : (j : ℕ) < (i : ℕ)
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using h)]
    rfl
  · rw [if_neg h, Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp only [Fin.coe_castSucc]; omega)]
    rfl
end PI.QnCovHatW
