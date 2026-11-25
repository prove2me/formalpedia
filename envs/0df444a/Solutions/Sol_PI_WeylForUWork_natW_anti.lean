-- Prove2me | solution 1 for PI.WeylForUWork.natW_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:40:22.332954+00:00
-- url     : https://prove2.me/submissions/fa11397b-af37-4ef2-909c-7c3ae7b989e5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaUnitary_NatWCastReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForUWork
open Finset PI.UpqRep Formalism.BasicNotions
namespace PI.WeylForUWork
theorem _root_.solution {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  unfold Formalism.BasicNotions.DomWeight.natW
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.2 hij) _)
end PI.WeylForUWork
