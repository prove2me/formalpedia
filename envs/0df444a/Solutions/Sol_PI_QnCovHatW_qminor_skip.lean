-- Prove2me | solution 1 for PI.QnCovHatW.qminor_skip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:07:37.07654+00:00
-- url     : https://prove2.me/submissions/5ccb08c3-07f9-427f-8ee9-e98a8d99930d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_InjDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_SkipOneEqSuccAbove
import Theorems.Thm_PI_QnCovHatW_skip_one_eq_succAbove

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
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A)
    (i j : Fin (m + 1)) (u : ℂ) :
    qminor E (skip1 i) (skip1 j) u = qminor (t := m) E i.succAbove j.succAbove u := by
  have h1 : (fun k : Fin m => skip1 (t := m + 1) i k) = i.succAbove := funext (skip_one_eq_succAbove i)
  have h2 : (fun k : Fin m => skip1 (t := m + 1) j k) = j.succAbove := funext (skip_one_eq_succAbove j)
  rw [← h1, ← h2]
end PI.QnCovHatW
