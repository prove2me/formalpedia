-- Prove2me | solution 1 for ULHC.valid_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:06:17.245414+00:00
-- url     : https://prove2.me/submissions/ab59b3cc-db83-4593-92dc-097835ce8b55

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_strip_sig


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {G : Finset Edge} {q : StripSpec} (hv : ValidStrip V G q)
    (hT : NoTypeIII V G) : 2 ≤ q.n := by
  by_contra hn
  obtain ⟨h1, hp, hc, hsep⟩ := hv
  have h1' : q.n = 1 := by omega
  have hc0 : IsCell V q.c := by have := hc 0 (by omega); rwa [cellJ_zero] at this
  obtain ⟨g1, g2, gb, gf⟩ := strip_sig hp (show 0 < q.n by omega)
  rw [cellJ_zero] at g1 g2 gb gf
  exact hsep (hT q.c hc0 q.s (gb.2 rfl) (gf.2 ⟨fun h => by omega, fun h => by omega⟩)
    (fun h => by have := g1.1 h; omega) (fun h => by have := g2.1 h; omega))
end ULHC
