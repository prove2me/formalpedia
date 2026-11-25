-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_LocJacTyp_card_Ioi__ab9c340c690c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:48:08.981252+00:00
-- url     : https://prove2.me/submissions/bc76d3ac-ee22-4843-9c3c-ad44fe5df69f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
open scoped Classical
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (r : ℕ) (i : Fin (r + 1)) :
    ((Finset.univ.filter fun j : Fin (r + 1) => i < j).card : ℝ) = (r : ℝ) - (i : ℕ) := by
  have h : (Finset.univ.filter fun j : Fin (r + 1) => i < j) = Finset.Ioi i := by ext j; simp
  rw [h, Fin.card_Ioi]
  have := i.is_le
  rw [show r + 1 - 1 - (i : ℕ) = r - (i : ℕ) by omega, Nat.cast_sub this]
end PI.UnitaryGroupMassFormula.LocJacTyp
