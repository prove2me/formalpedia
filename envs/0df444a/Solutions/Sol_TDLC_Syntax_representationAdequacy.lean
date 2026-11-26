-- Prove2me | solution 1 for TDLC.Syntax.representationAdequacy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:27:53.468873+00:00
-- url     : https://prove2.me/submissions/f44878aa-a225-4537-a70a-291ceafa4102

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Syntax
import Theorems.Thm_TDLC_Syntax_erase_elaborate

set_option autoImplicit true
open TDLC TDLC.Syntax
namespace TDLC.Syntax
theorem _root_.solution (Γ : List Ty) (r : Raw) (a : Ty) :
    Nonempty (HasType Γ r a) ↔ ∃ t : Tm Γ a, erase t = r := by
  constructor
  · intro ⟨h⟩
    exact ⟨elaborate h, erase_elaborate h⟩
  · rintro ⟨t, rfl⟩
    exact ⟨eraseTyped t⟩
end TDLC.Syntax
