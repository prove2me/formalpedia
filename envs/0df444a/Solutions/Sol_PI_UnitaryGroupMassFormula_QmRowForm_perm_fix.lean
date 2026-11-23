-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmRowForm.perm_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:16.843109+00:00
-- url     : https://prove2.me/submissions/b2b7c48e-5ab9-4021-be58-5f056b9b948a

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
theorem _root_.solution {m : ℕ} (i : Fin m) (k : Fin (m + 1)) (h1 : (k : ℕ) ≠ i) (h2 : (k : ℕ) ≠ (i : ℕ) + 1) :
    Equiv.swap i.castSucc i.succ k = k := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    apply h1
    rw [h]
    simp
  · intro h
    apply h2
    rw [h]
    simp
end PI.UnitaryGroupMassFormula.QmRowForm
