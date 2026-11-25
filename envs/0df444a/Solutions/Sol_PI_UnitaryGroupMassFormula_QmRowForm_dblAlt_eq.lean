-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmRowForm.dblAlt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:13.878909+00:00
-- url     : https://prove2.me/submissions/15763cdf-64a2-43cf-9fd6-f620a407cf03

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_PermutedRowProductSplit

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
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (x : Fin t → ℂ) :
    doubleRowFormSum E a b x = ∑ σ : Equiv.Perm (Fin t), ∑ τ : Equiv.Perm (Fin t),
      pε σ τ * (List.ofFn (pF E a b x σ τ)).prod := rfl
end PI.UnitaryGroupMassFormula.QmRowForm
