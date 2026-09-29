-- Prove2me | solution 1 for R03SP01C3C3Complement.c3c3_complement_has_factor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:52:32.587835+00:00
-- url     : https://prove2.me/submissions/a222baca-72f6-4d55-a003-1d1e581dcf19

import Mathlib
import Definitions.Def_r03_defs_191207a298_r03_sp01_c3c3_complement_lean_candidate_v1

/-!
Candidate-only generic C3 disjoint union C3 complement lemma for SP01.

The supplied equivalence `parts` labels two triples by indices 0..2 and 3..5;
the hypothesis says that no complement edge crosses these two triples.  The
explicit permutation then realizes the two paths (A0,B0,A1) and (B1,A2,B2).
The cubic-to-complement classification is intentionally not assumed here.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace R03SP01C3C3Complement

lemma graph_adj_of_complement_not_adj {G : SimpleGraph V} {u v : V}
    (hne : u ≠ v) (hnot : ¬ Gᶜ.Adj u v) : G.Adj u v := by
  by_contra h
  exact hnot ((G.compl_adj u v).mpr ⟨hne, h⟩)

lemma parts_adj_of_distinct_parts {G : SimpleGraph V} {parts : Fin 6 ≃ V}
    (hparts : ComplementHasTwoParts G parts) (u v : Fin 6)
    (hcross : u.val / 3 ≠ v.val / 3) :
    G.Adj (parts u) (parts v) := by
  apply graph_adj_of_complement_not_adj
  · exact parts.injective.ne (by
      intro huv
      apply hcross
      simpa [huv]
  )
  · exact hparts u v hcross

end R03SP01C3C3Complement

open R03SP01C3C3Complement
theorem solution {G : SimpleGraph V}
    {parts : Fin 6 ≃ V} (hparts : ComplementHasTwoParts G parts) :
    Nonempty (LocalP3Factor G) := by
  have h03 : G.Adj (parts 0) (parts 3) :=
    parts_adj_of_distinct_parts hparts 0 3 (by decide)
  have h31 : G.Adj (parts 3) (parts 1) :=
    parts_adj_of_distinct_parts hparts 3 1 (by decide)
  have h42 : G.Adj (parts 4) (parts 2) :=
    parts_adj_of_distinct_parts hparts 4 2 (by decide)
  have h25 : G.Adj (parts 2) (parts 5) :=
    parts_adj_of_distinct_parts hparts 2 5 (by decide)
  refine ⟨{
    blockCount := 2
    place := c3c3Place parts
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    fin_cases i
    · simpa [c3c3Place, triEquiv, triTo, finProdFinEquiv] using h03
    · simpa [c3c3Place, triEquiv, triTo, finProdFinEquiv] using h42
  · intro i
    fin_cases i
    · simpa [c3c3Place, triEquiv, triTo, finProdFinEquiv] using h31
    · simpa [c3c3Place, triEquiv, triTo, finProdFinEquiv] using h25
