-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmRowForm.Tm_opE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:12.152424+00:00
-- url     : https://prove2.me/submissions/5db5b963-3cd4-46c0-91e1-4b3bd0ac7443

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_DoubleRowIncreasing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmRowForm
namespace PI.UnitaryGroupMassFormula.QmRowForm
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x : ℂ) (a b : Fin n) :
    Tm (opE E) x a b = MulOpposite.op (Tm E x b a) := by
  unfold Tm opE
  by_cases h : a = b
  · subst h
    simp
  · simp [h, Ne.symm h]
end PI.UnitaryGroupMassFormula.QmRowForm
