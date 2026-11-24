-- Prove2me | solution 1 for ULHC.mem_cells
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:49.625322+00:00
-- url     : https://prove2.me/submissions/8cd9c629-178a-4ee4-9ca0-939b6c844aee

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D

set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {c : Pt} : c ∈ cells V ↔ IsCell V c := by
  unfold cells; rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
end ULHC
