-- Prove2me | solution 1 for P2M_ConfFamily_inter_diff_union__310b7debc330
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:03:37.016426+00:00
-- url     : https://prove2.me/submissions/6d370d6d-719b-4764-999a-52e145aa8433

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Stable_LTSI
import Theorems.Thm_ConfFamily_inter_diff_union
import Theorems.Thm_Bisimilar_symm
import Theorems.Thm_ConfFamily_Indep_symm


set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
variable {F}
namespace ConfFamily
theorem _root_.solution {c : Set F.Event} {e₁ e₂ : F.Event}
    (he₁ : e₁ ∈ c) (hne : e₁ ≠ e₂) :
    ((c \ {e₁}) ∩ (c \ {e₂})) ∪ {e₁} = c \ {e₂} := by
  rw [Set.inter_comm]; exact inter_diff_union he₁ hne.symm
end ConfFamily
