-- Prove2me | solution 1 for PI.AddIntG.Wk.glue_holds_var
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:55.53207+00:00
-- url     : https://prove2.me/submissions/27ad30db-b422-489a-bdf1-9c727d274dbe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GuLine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Theorems.Thm_PI_AddIntG_Wk_add_eq_of
import Theorems.Thm_PI_AddIntG_Wk_exists_intS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution : Glue := by
  unfold PI.AddIntG.Glue PI.AddIntG.Target
  intro hlaw p _ W wq ex ha1 ha2 ha3 ha4 ha6 hW hex0 hex
  unfold PI.AddIntG.KeyF at hlaw
  obtain ⟨S, hS⟩ := exists_intS p
  refine ⟨?_, ?_⟩
  · obtain ⟨F, hFS, hF0, hF⟩ := hlaw p S W wq ((hS _).2 ha1) ((hS _).2 ha2) ((hS _).2 ha3)
      ((hS _).2 ha4) ((hS _).2 ha6) hW
    rw [add_eq_of hW hex0 hex F hF0 hF]
    intro n
    exact (hS _).1 (hFS n)
  · rintro ⟨h1, h2, h3, h4, h6⟩
    obtain ⟨F, hFS, hF0, hF⟩ := hlaw p (PI.AddIntG.Wp p) W wq h1 h2 h3 h4 h6 hW
    rw [add_eq_of hW hex0 hex F hF0 hF]
    exact hFS
end PI.AddIntG.Wk
