-- Prove2me | solution 1 for ULHC.link_cells
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:57:56.288116+00:00
-- url     : https://prove2.me/submissions/aca149a7-5af1-4d87-ae00-bd87e73a59c3

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution {b c : StripSpec} (h : CR2 V G b c) :
    1 ≤ c.n ∧ ∀ j < c.n, IsCell V (cellJ c.c c.s j) := by
  obtain ⟨_, _, h1, _, hc, _⟩ := h
  exact ⟨h1, hc⟩
end ULHC
