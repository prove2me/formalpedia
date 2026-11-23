-- Prove2me | solution 1 for PosIndexNash.PPADS.oriented_lemke_howson_reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:48:09.150834+00:00
-- url     : https://prove2.me/submissions/7af19c3b-788a-4c77-b9a2-5a50a23d89db
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CardinalMatching_SearchReduces
import Theorems.Thm_PosIndexNash_PPADS_lemma_3_1
import Theorems.Thm_PosIndexNash_PPADS_lh_basis_sink_circuits
import Theorems.Thm_PosIndexNash_PPADS_lh_completely_labeled_answer_decoder

open PosIndexNash.PPADS

theorem solution : CardinalMatching.SearchReduces PositivePayoffNash SinkOfLine := by
  obtain ⟨f, hf, hcircuits⟩ := lh_basis_sink_circuits
  obtain ⟨g, hg, hdecode⟩ := lh_completely_labeled_answer_decoder
  refine ⟨f, g, hf, hg, ?_⟩
  intro s hs
  rcases hs with ⟨G, hm, hn, rfl, hA, hB, hND⟩
  obtain ⟨l, ⟨S, P, hcode, hSOL⟩, hsinks⟩ :=
    hcircuits G hm hn hA hB hND
  constructor
  · exact ⟨S, P, hSOL, hcode⟩
  · intro z hz
    rcases hz with ⟨S', P', hSOL', hcode', hzlen, hzbad⟩
    obtain ⟨v, hCL, hv0, hzrep, hnout⟩ :=
      hsinks S' P' hcode' hSOL' z hzlen hzbad
    obtain ⟨x, y, hgxy, hx, hy, hNE, hindex⟩ :=
      hdecode G hm hn hA hB hND z v hCL hv0 hzrep
    have hend := (PosIndexNash.PPADS.lemma_3_1).1 G hm hn hA hB hND l
    have hindex_v : shapleyIndex (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ))
        (lhRowStrategy v) (lhColStrategy v) = 1 := by
      have hindex_v' : shapleyIndex (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ))
          (lhRowStrategy v) (lhColStrategy v) = -1 ∨
          shapleyIndex (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ))
            (lhRowStrategy v) (lhColStrategy v) = 1 := by
        simpa only [hx, hy] using hindex
      rcases hindex_v' with hneg | hpos
      · exact (hnout ((hend.2.2 v hCL hv0).1 hneg).1.exists).elim
      · exact hpos
    refine ⟨G, x, y, hm, hn, rfl, hA, hB, hND, hgxy, hNE, ?_⟩
    simpa only [hx, hy] using hindex_v
