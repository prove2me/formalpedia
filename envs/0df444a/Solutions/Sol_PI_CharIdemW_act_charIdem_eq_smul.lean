-- Prove2me | solution 1 for PI.CharIdemW.act_charIdem_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:58.969801+00:00
-- url     : https://prove2.me/submissions/c578c1b3-8166-41e8-a784-970e4d407c0f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar
import Theorems.Thm_PI_CharIdemW_act_charIdem
import Theorems.Thm_PI_CharIdemW_comm_of_class
import Theorems.Thm_PI_CharIdemW_schur_scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open PI PI.CharIdemW
open PI.CharIdem
variable {G : Type} [Group G] [Fintype G]
namespace PI.CharIdemW
theorem _root_.solution (V W : FDRep ℂ G) [Simple W] :
    ∃ c : ℂ, act W (charIdem V) = c • 1 := by
  apply schur_scalar W
  intro g
  rw [act_charIdem]
  refine comm_of_class W
    (fun x => (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * V.character x⁻¹) ?_ g
  intro x h
  rw [show (h * x * h⁻¹)⁻¹ = h * x⁻¹ * h⁻¹ by group, FDRep.char_conj]
end PI.CharIdemW
