-- Prove2me | solution 1 for ULHC.Ends.inV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:38.724431+00:00
-- url     : https://prove2.me/submissions/e3589421-b94c-4815-9572-976fd8b2f4c1

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
namespace Ends
theorem _root_.solution {V : Finset Pt} {e : Edge} {a b : Pt} (h : Ends e a b) (hV : e.p ∈ V ∧ e.q ∈ V) :
    a ∈ V ∧ b ∈ V := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [← h1, ← h2] <;> tauto
end Ends
end ULHC
