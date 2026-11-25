-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.sum_sA_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:41:50.736407+00:00
-- url     : https://prove2.me/submissions/862d9e06-3af0-45ae-9430-3c9f0da1c443

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipTwoSuccAboveComp

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull PI.UnitaryGroupMassFormula.QmBorderFull.Four
open PI
namespace PI.UnitaryGroupMassFormula.QmBorderFull.Four
theorem _root_.solution {M : Type*} [AddCommMonoid M] {k : ℕ} (w : Fin (k + 1)) (g : Fin (k + 1) → M) :
    ∑ w' : Fin (k + 1), (if w ≠ w' then g w' else 0) = ∑ j : Fin k, g (w.succAbove j) := by
  rw [Fin.sum_univ_succAbove _ w, if_neg (not_not.mpr rfl), zero_add]
  exact Finset.sum_congr rfl fun j _ => if_pos (Fin.succAbove_ne w j).symm
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
