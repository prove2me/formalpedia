-- Prove2me | solution 1 for ShiShallow.length_filter_meets_le
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:31:27.9544+00:00
-- url     : https://prove2.me/submissions/a2b4ce8a-8e33-4bed-84ed-a02081c86e1f

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Shallow quantum circuits and causal cones.

MODIFICATIONS made for publication on Prove2me: the enclosing `namespace` is replaced by `section`+`open` and the target theorem is renamed to `solution`;
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Circuit

section
open ShiShallow

theorem solution {n : ℕ} (l : List (Instr n)) (hl : LayerOk l) :
    ∀ S : Finset (Fin n),
      (l.filter (fun g => decide (g.support ∩ S).Nonempty)).length ≤ S.card := by
  induction l with
  | nil => intro S; simp
  | cons g t ih =>
      intro S
      rw [LayerOk, List.pairwise_cons] at hl
      obtain ⟨hdisj, ht⟩ := hl
      by_cases h : (g.support ∩ S).Nonempty
      · rw [List.filter_cons_of_pos (by simpa using h), List.length_cons]
        have hfe : t.filter (fun b => decide (b.support ∩ S).Nonempty)
            = t.filter (fun b => decide (b.support ∩ (S \ g.support)).Nonempty) := by
          refine List.filter_congr ?_
          intro b hb
          have hd : Disjoint b.support g.support := (hdisj b hb).symm
          simp only [decide_eq_decide]
          constructor
          · rintro ⟨a, ha⟩
            rw [Finset.mem_inter] at ha
            refine ⟨a, Finset.mem_inter.mpr ⟨ha.1, Finset.mem_sdiff.mpr ⟨ha.2, ?_⟩⟩⟩
            exact fun hg => Finset.disjoint_left.mp hd ha.1 hg
          · rintro ⟨a, ha⟩
            rw [Finset.mem_inter, Finset.mem_sdiff] at ha
            exact ⟨a, Finset.mem_inter.mpr ⟨ha.1, ha.2.1⟩⟩
        rw [hfe]
        obtain ⟨a, ha⟩ := h
        rw [Finset.mem_inter] at ha
        have hlt : (S \ g.support).card < S.card := by
          refine Finset.card_lt_card ⟨Finset.sdiff_subset, ?_⟩
          intro hsub
          exact (Finset.mem_sdiff.mp (hsub ha.2)).2 ha.1
        have h1 := ih ht (S \ g.support)
        omega
      · rw [List.filter_cons_of_neg (by simpa using h)]
        exact ih ht S

end
