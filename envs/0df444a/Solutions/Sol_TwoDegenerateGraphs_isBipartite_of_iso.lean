-- Prove2me | solution 1 for TwoDegenerateGraphs.isBipartite_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/b9e4dbba-a4f6-41ee-972c-91b09a08b575

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : G.IsBipartite) : H.IsBipartite := by
  obtain ⟨coloring⟩ := hG
  exact ⟨coloring.comp e.symm.toHom⟩
end TwoDegenerateGraphs
