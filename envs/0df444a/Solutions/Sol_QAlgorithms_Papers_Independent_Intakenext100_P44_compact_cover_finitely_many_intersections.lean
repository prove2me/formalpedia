-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P44.compact_cover_finitely_many_intersections
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:26:17.077959+00:00
-- url     : https://prove2.me/submissions/dbc0627c-1fe3-49c1-8858-7f1f9f339300

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P44

noncomputable section

open Set

open scoped ContDiff

theorem solution
    {M I : Type*} [TopologicalSpace M] (u : I → Set M)
    (hcover : (⋃ i, u i) = Set.univ) (hcompact : ∀ i, IsCompact (u i))
    (hfinite : LocallyFinite u) (i : I) :
    {j : I | (u i ∩ u j).Nonempty}.Finite := by
  have h := hfinite.finite_nonempty_inter_compact (hcompact i)
  refine h.subset ?_
  intro j hj
  simp only [Set.mem_setOf_eq] at hj ⊢
  rwa [Set.inter_comm]

end
