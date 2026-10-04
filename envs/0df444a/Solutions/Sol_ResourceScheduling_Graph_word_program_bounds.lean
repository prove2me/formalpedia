-- Prove2me | solution 1 for ResourceScheduling.Graph.word_program_bounds
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:24:55.830683+00:00
-- url     : https://prove2.me/submissions/26c14000-ee22-4942-b099-3fe8527426d4

import Definitions.Def_ResourceScheduling_Graph_WordProgram
import Theorems.Thm_ResourceScheduling_Graph_unary_codec_correct

set_option autoImplicit false
open ResourceScheduling.Graph

private theorem flat_bound {α β : Type} (xs : List α) (f : α → List β) (n : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ n) : (xs.flatMap f).length ≤ xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul,
      Nat.one_mul]
    omega

/-- Every parsed loop bound and resource index is bounded by the actual input length. -/
theorem solution (w : List Letter) (t : ℕ) (bits : List Letter)
    (h : readUnary w = some (t, bits)) :
    t + 1 + bits.length = w.length ∧
    (wordNonEdges (3 * t) bits).length ≤ 9 * w.length ^ 2 ∧
    (∀ p ∈ wordNonEdges (3 * t) bits,
      p.1 < p.2 ∧ p.2 < 3 * t ∧ bits.getD (p.1 * (3 * t) + p.2) Letter.sep ≠ Letter.one) := by
  have he := congrArg List.length (unary_codec_correct.2.1 w t bits h)
  simp only [List.length_append, unary, List.length_replicate, List.length_singleton] at he
  refine ⟨he.symm, ?_, ?_⟩
  · have hb : (wordNonEdges (3 * t) bits).length ≤ (3 * t) * (3 * t) := by
      unfold wordNonEdges
      apply le_trans (flat_bound _ _ (3 * t) ?_) (by simp)
      intro i hi
      simpa only [List.length_map, List.length_range] using
        List.length_filter_le (fun j => decide
          (i < j ∧ bits.getD (i * (3 * t) + j) Letter.sep ≠ Letter.one)) (List.range (3 * t))
    have ht : t ≤ w.length := by omega
    nlinarith
  · rintro ⟨i, j⟩ hp
    simp only [wordNonEdges, List.mem_flatMap, List.mem_map, List.mem_filter,
      List.mem_range, decide_eq_true_eq, Prod.mk.injEq] at hp
    obtain ⟨a, _, b, ⟨hb, hab, hzero⟩, rfl, rfl⟩ := hp
    exact ⟨hab, hb, hzero⟩

#print axioms solution
