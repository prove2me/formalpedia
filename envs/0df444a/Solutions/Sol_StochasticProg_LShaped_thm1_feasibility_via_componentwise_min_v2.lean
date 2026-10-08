-- Prove2me | solution 1 for StochasticProg.LShaped.thm1_feasibility_via_componentwise_min_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T15:23:17.701857+00:00
-- url     : https://prove2.me/submissions/623e2e96-001e-4f57-aad0-84d2e457163c

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_StochasticProg_LShaped_Algorithm



namespace StochasticProg.LShaped

open StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

lemma t1_foldr_top (l : List EReal) : l.foldr bookAdd 0 = ⊤ ↔ ⊤ ∈ l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, List.mem_cons]
    unfold bookAdd
    split_ifs with h
    · rcases h with h | h
      · simp [h]
      · simp [ih.mp h]
    · push_neg at h
      constructor
      · intro h'; exact absurd h' (EReal.add_ne_top h.1 h.2)
      · rintro (h' | h')
        · exact absurd h'.symm h.1
        · exact absurd (ih.mpr h') h.2

lemma t1_QVal_top (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ) (k : Fin K) :
    QVal inst x k = ⊤ ↔ ¬ ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧
      Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x := by
  unfold QVal
  rw [sInf_eq_top]
  constructor
  · rintro h ⟨y, hy, hW⟩
    exact EReal.coe_ne_top _ (h _ ⟨y, hy, hW, rfl⟩)
  · rintro h z ⟨y, hy, hW, rfl⟩
    exact absurd ⟨y, hy, hW⟩ h

lemma t1_mem_K2 (inst : Instance n1 n2 m1 m2 K) (hp_pos : ∀ k, 0 < inst.p k) (x : Fin n1 → ℝ) :
    x ∈ K2 inst ↔ ∀ k, ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧
      Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x := by
  unfold K2 Q
  simp only [Set.mem_setOf_eq, ne_eq, t1_foldr_top, List.mem_ofFn, Set.mem_range, not_exists]
  apply forall_congr'
  intro k
  rw [← not_iff_not, not_not, ← t1_QVal_top]
  constructor
  · intro h
    rw [EReal.mul_eq_top] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨_, h2⟩
    · exact absurd h1 (EReal.coe_ne_bot _)
    · exact absurd h1 (not_lt.mpr (EReal.coe_nonneg.mpr (inst.hp_nonneg k)))
    · exact absurd h1 (EReal.coe_ne_top _)
    · exact h2
  · intro h
    rw [h]
    exact EReal.mul_top_of_pos (EReal.coe_pos.mpr (hp_pos k))

theorem thm1_core
    (inst : Instance n1 n2 m1 m2 K) (hK : 0 < K) (hp_pos : ∀ k, 0 < inst.p k)
    (T0 : Matrix (Fin m2) (Fin n1) ℝ) (hT : ∀ k, inst.T k = T0)
    (hWpos : ∀ t : Fin m2 → ℝ, (∀ i, 0 ≤ t i) → posW inst t)
    (a : Fin m2 → ℝ) (ha : ∀ i, a i = sInf {v : ℝ | ∃ k : Fin K, v = inst.h k i})
    (ℓ : Fin K) (haℓ : a = inst.h ℓ) (x : Fin n1 → ℝ) :
    x ∈ K2 inst ↔
      ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧ Matrix.mulVec inst.W y = a - Matrix.mulVec T0 x := by
  rw [t1_mem_K2 inst hp_pos]
  constructor
  · intro h
    obtain ⟨y, hy, hW⟩ := h ℓ
    exact ⟨y, hy, by rw [hW, hT, haℓ]⟩
  · rintro ⟨y, hy, hW⟩ k
    have hle : ∀ i, 0 ≤ (inst.h k - a) i := by
      intro i
      simp only [Pi.sub_apply, sub_nonneg]
      rw [ha i]
      apply csInf_le
      · refine ⟨inst.h ℓ i, ?_⟩
        rintro v ⟨k', rfl⟩
        have := ha i
        rw [haℓ] at this
        rw [this]
        apply csInf_le
        · exact (Set.finite_range (fun k' : Fin K => inst.h k' i)).bddBelow.mono
            (by rintro v ⟨k'', rfl⟩; exact ⟨k'', rfl⟩)
        · exact ⟨k', rfl⟩
      · exact ⟨k, rfl⟩
    obtain ⟨y', hy', hW'⟩ := hWpos _ hle
    refine ⟨y + y', fun i => add_nonneg (hy i) (hy' i), ?_⟩
    rw [Matrix.mulVec_add, hW, hW', hT]
    abel
end StochasticProg.LShaped

open StochasticProg.LShaped
open StochasticProg.Recourse

theorem solution {n1 n2 m1 m2 K : ℕ}
    (inst : Instance n1 n2 m1 m2 K) (hK : 0 < K) (hp_pos : ∀ k, 0 < inst.p k)
    (T0 : Matrix (Fin m2) (Fin n1) ℝ) (hT : ∀ k, inst.T k = T0)
    (hWpos : ∀ t : Fin m2 → ℝ, (∀ i, 0 ≤ t i) → posW inst t)
    (a : Fin m2 → ℝ) (ha : ∀ i, a i = sInf {v : ℝ | ∃ k : Fin K, v = inst.h k i})
    (ℓ : Fin K) (haℓ : a = inst.h ℓ) (x : Fin n1 → ℝ) :
    x ∈ K2 inst ↔
      ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧ Matrix.mulVec inst.W y = a - Matrix.mulVec T0 x := by
  exact thm1_core inst hK hp_pos T0 hT hWpos a ha ℓ haℓ x
