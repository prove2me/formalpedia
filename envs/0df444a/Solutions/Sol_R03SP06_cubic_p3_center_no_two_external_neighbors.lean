-- Prove2me | solution 1 for R03SP06.cubic_p3_center_no_two_external_neighbors
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:03:40.566395+00:00
-- url     : https://prove2.me/submissions/5f455355-c416-4aab-a4fe-a593b6946bdf

import Mathlib

/-!
Candidate formalization of the local counting bottleneck used in the
3-connected cubic P3-deletion connectivity lemma.  It proves only the local
fact that the center of a P3 has exactly one neighbor outside its two
endpoints in a cubic graph.  The global component argument remains outside
this file.
-/

namespace R03SP06

variable {V : Type} [Fintype V] [DecidableEq V]

/-- In a cubic graph, the center of a P3 has one remaining neighbor outside
its two endpoints.  The degree hypothesis is written as the cardinality of
the finite neighbor filter, avoiding any auxiliary neighbor-set instance. -/
theorem cubic_p3_center_external_neighbor_card
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c)
    (hdeg : (Finset.univ.filter (fun w : V => G.Adj b w)).card = 3) :
    ((Finset.univ.filter (fun w : V => G.Adj b w)) \ {a, c}).card = 1 := by
  let N : Finset V := Finset.univ.filter (fun w : V => G.Adj b w)
  have hsub : {a, c} ⊆ N := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simpa [N] using (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.symm⟩)
    · simpa [N] using (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbc⟩)
  have hN : N.card = 3 := by
    simpa [N] using hdeg
  rw [show ((Finset.univ.filter (fun w : V => G.Adj b w)) \ {a, c}) = N \ {a, c} by rfl]
  rw [Finset.card_sdiff_of_subset hsub, hN]
  simp [hac]

#print axioms R03SP06.cubic_p3_center_external_neighbor_card


end R03SP06

open R03SP06
variable {V : Type} [Fintype V] [DecidableEq V]
theorem solution
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b c x y : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c)
    (hbx : G.Adj b x) (hby : G.Adj b y) (hxy : x ≠ y)
    (hxa : x ≠ a) (hxc : x ≠ c) (hya : y ≠ a) (hyc : y ≠ c)
    (hdeg : (Finset.univ.filter (fun w : V => G.Adj b w)).card = 3) :
    False := by
  let N : Finset V := Finset.univ.filter (fun w : V => G.Adj b w)
  have hone : (N \ {a, c}).card = 1 := by
    simpa [N] using
      (cubic_p3_center_external_neighbor_card hab hbc hac hdeg)
  have hxy_sub : ({x, y} : Finset V) ⊆ N \ {a, c} := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · simpa [N] using (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbx⟩)
      · simp [hxa, hxc]
    · refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · simpa [N] using (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hby⟩)
      · simp [hya, hyc]
  have hcard := Finset.card_le_card hxy_sub
  rw [hone] at hcard
  simp [hxy] at hcard

