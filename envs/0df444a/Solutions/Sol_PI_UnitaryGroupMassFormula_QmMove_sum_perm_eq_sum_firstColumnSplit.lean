-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.sum_perm_eq_sum_firstColumnSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:16.420058+00:00
-- url     : https://prove2.me/submissions/3a1b87b9-2480-4c7b-b5fe-846dee0aac95

import Definitions.Def_Formalism_PeriodIntegrals_QmDefs
import Definitions.Def_Formalism_PeriodIntegrals_QmMove
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_firstColumnSplit_bijective

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
theorem _root_.solution {M : Type*} [AddCommMonoid M] (m : ℕ) (g : Equiv.Perm (Fin (m + 1)) → M) :
    ∑ τ, g τ = ∑ j : Fin (m + 1), ∑ ρ : Equiv.Perm (Fin m), g (phi0 m (j, ρ)) := by
  rw [(Fintype.sum_bijective (phi0 m) (firstColumnSplit_bijective m) (fun p => g (phi0 m p)) g (fun _ => rfl)).symm,
    Fintype.sum_prod_type]
end PI.UnitaryGroupMassFormula.QmMove
