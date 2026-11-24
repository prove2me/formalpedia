-- Prove2me | solution 1 for ULHC.Ends.isEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:43.811149+00:00
-- url     : https://prove2.me/submissions/812a688c-e000-4f4a-97f8-3a26a022eca6

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
namespace Ends
theorem _root_.solution {V : Finset Pt} {e : Edge} {a b : Pt} (h : Ends e a b) (ha : a ∈ V)
    (hb : b ∈ V) : IsEdge V e := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> unfold IsEdge <;> rw [h1, h2] <;> tauto
end Ends
end ULHC
