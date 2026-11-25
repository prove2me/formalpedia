-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.firstColumnSplit_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:50.410618+00:00
-- url     : https://prove2.me/submissions/a4daf43d-ce43-4b76-a290-45cdc0b50bd8

import Definitions.Def_Formalism_PeriodIntegrals_QmDefs
import Definitions.Def_Formalism_PeriodIntegrals_QmMove
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_firstColumnSplit_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_firstColumnSplit_succ

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmMove
namespace PI.UnitaryGroupMassFormula.QmMove
theorem _root_.solution (m : ℕ) : Function.Bijective (phi0 m) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨j, τ⟩ ⟨j', τ'⟩ h
    have hj : j = j' := by
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ 0) h
      simpa [firstColumnSplit_zero] using this
    subst hj
    have : τ = τ' := by
      refine Equiv.ext fun k => ?_
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ k.succ) h
      simp only [firstColumnSplit_succ] at this
      exact Fin.succAbove_right_inj.mp this
    rw [this]
  · simp [Fintype.card_prod, Fintype.card_perm, Nat.factorial_succ]
end PI.UnitaryGroupMassFormula.QmMove
