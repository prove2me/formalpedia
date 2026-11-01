-- Prove2me | solution 1 for StrongPerfectGraph.Main.recalcitrant_bipartite
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:36:01.542034+00:00
-- url     : https://prove2.me/submissions/c6f5aae3-bcd3-4e66-882b-64a5faf9ff2f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsRecalcitrant
import Theorems.Thm_StrongPerfectGraph_Main_berge_decomposition

open StrongPerfectGraph.Main

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsRecalcitrant G) :
    G.IsBipartite ∨ Gᶜ.IsBipartite := by
  rcases hG with ⟨hBerge, hNL, hNLc, hNDS, hN2J, hN2Jc, hNHP, hNBSP⟩
  rcases berge_decomposition G hBerge with hBasic | h2J | h2Jc | hHP | hBSP
  · rcases hBasic with hBip | hBipc | ⟨n, H, _, hIso⟩ | ⟨n, H, _, hIsoc⟩ | hDS
    · exact Or.inl hBip
    · exact Or.inr hBipc
    · exact absurd ⟨n, H, hIso⟩ hNL
    · exact absurd ⟨n, H, hIsoc⟩ hNLc
    · exact absurd hDS hNDS
  · exact absurd h2J hN2J
  · exact absurd h2Jc hN2Jc
  · exact absurd hHP hNHP
  · exact absurd hBSP hNBSP
