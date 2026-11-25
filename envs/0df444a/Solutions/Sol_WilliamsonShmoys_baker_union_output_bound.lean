-- Prove2me | solution 1 for WilliamsonShmoys.baker_union_output_bound
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T10:16:49.466122+00:00
-- url     : https://prove2.me/submissions/941558d0-66a1-462d-a5fa-d843f0c37da6

import Mathlib
import Theorems.Thm_WilliamsonShmoys_indepSet_disjoint_union_split

set_option autoImplicit false

open Classical in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (lvl : Fin n → ℕ) (k : ℕ) (weight : Fin n → ℝ)
    (A : Finset (Fin k × Fin n))
    (hA : (SimpleGraph.fromRel (fun (x y : Fin k × Fin n) => x.1 = y.1 ∧ G.Adj x.2 y.2 ∧
        lvl x.2 % k ≠ x.1.val ∧ lvl y.2 % k ≠ x.1.val)).IsIndepSet (A : Set (Fin k × Fin n)))
    (hopt : ∀ S : Finset (Fin k × Fin n),
      (SimpleGraph.fromRel (fun (x y : Fin k × Fin n) => x.1 = y.1 ∧ G.Adj x.2 y.2 ∧
        lvl x.2 % k ≠ x.1.val ∧ lvl y.2 % k ≠ x.1.val)).IsIndepSet (S : Set (Fin k × Fin n)) →
      ∑ x ∈ S, (if lvl x.2 % k ≠ x.1.val then weight x.2 else 0) ≤
        ∑ x ∈ A, (if lvl x.2 % k ≠ x.1.val then weight x.2 else 0))
    (cs : Fin k)
    (hbest : ∀ c : Fin k, ∑ x ∈ A.filter (fun x => x.1 = c), (if lvl x.2 % k ≠ x.1.val then weight x.2 else 0) ≤
      ∑ x ∈ A.filter (fun x => x.1 = cs), (if lvl x.2 % k ≠ x.1.val then weight x.2 else 0)) :
    G.IsIndepSet ((Finset.univ.filter (fun v => (cs, v) ∈ A ∧ lvl v % k ≠ cs.val) : Finset (Fin n)) : Set (Fin n)) ∧
    ∀ j < k, ∀ S : Finset (Fin n),
      (SimpleGraph.fromRel (fun u v => G.Adj u v ∧ lvl u % k ≠ j ∧ lvl v % k ≠ j)).IsIndepSet (S : Set (Fin n)) →
      ∑ i ∈ S, (if lvl i % k ≠ j then weight i else 0) ≤
        ∑ i ∈ Finset.univ.filter (fun v => (cs, v) ∈ A ∧ lvl v % k ≠ cs.val), weight i := by
  set H : Fin k → SimpleGraph (Fin n) := fun c =>
    SimpleGraph.fromRel (fun u v => G.Adj u v ∧ lvl u % k ≠ c.val ∧ lvl v % k ≠ c.val) with hH
  have hgr : SimpleGraph.fromRel (fun (x y : Fin k × Fin n) => x.1 = y.1 ∧ G.Adj x.2 y.2 ∧
        lvl x.2 % k ≠ x.1.val ∧ lvl y.2 % k ≠ x.1.val) =
      SimpleGraph.fromRel (fun (u v : Fin k × Fin n) => u.1 = v.1 ∧ (H u.1).Adj u.2 v.2) := by
    ext x y
    simp only [SimpleGraph.fromRel_adj, hH, ne_eq]
    constructor
    · rintro ⟨hne, h | h⟩
      · refine ⟨hne, Or.inl ⟨h.1, ?_, Or.inl ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩⟩
        intro he; exact hne (Prod.ext h.1 he)
      · refine ⟨hne, Or.inr ⟨h.1, ?_, Or.inl ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩⟩
        intro he; exact hne (Prod.ext h.1.symm he.symm)
    · rintro ⟨hne, ⟨h1, -, h | h⟩ | ⟨h1, -, h | h⟩⟩
      · exact ⟨hne, Or.inl ⟨h1, h.1, h.2.1, h.2.2⟩⟩
      · exact ⟨hne, Or.inl ⟨h1, h.1.symm, h.2.2, h.2.1⟩⟩
      · exact ⟨hne, Or.inr ⟨h1, h.1, h.2.1, h.2.2⟩⟩
      · exact ⟨hne, Or.inr ⟨h1, h.1.symm, h.2.2, h.2.1⟩⟩
  refine ⟨?_, ?_⟩
  · intro v hv w hw hvw hadj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv hw
    apply hA hv.1 hw.1 (fun h => hvw (congrArg Prod.snd h))
    rw [SimpleGraph.fromRel_adj]
    exact ⟨fun h => hvw (congrArg Prod.snd h), Or.inl ⟨rfl, hadj, hv.2, hw.2⟩⟩
  · intro j hj S hS
    set w' : Fin k × Fin n → ℝ := fun x => if lvl x.2 % k ≠ x.1.val then weight x.2 else 0 with hw'
    have hA' : (SimpleGraph.fromRel (fun (u v : Fin k × Fin n) => u.1 = v.1 ∧ (H u.1).Adj u.2 v.2)).IsIndepSet
        (A : Set (Fin k × Fin n)) := by rw [← hgr]; exact hA
    have hopt' : ∀ S : Finset (Fin k × Fin n),
        (SimpleGraph.fromRel (fun (u v : Fin k × Fin n) => u.1 = v.1 ∧ (H u.1).Adj u.2 v.2)).IsIndepSet
          (S : Set (Fin k × Fin n)) → ∑ x ∈ S, w' x ≤ ∑ x ∈ A, w' x := by
      intro S hS; rw [← hgr] at hS; exact hopt S hS
    have hSj : (H ⟨j, hj⟩).IsIndepSet (S : Set (Fin n)) := by simpa [hH] using hS
    have h1 := WilliamsonShmoys.indepSet_disjoint_union_split H w' A hA' hopt' ⟨j, hj⟩ S hSj
    have h2 := hbest ⟨j, hj⟩
    have h3 : ∑ x ∈ A.filter (fun x => x.1 = cs), w' x =
        ∑ i ∈ Finset.univ.filter (fun v => (cs, v) ∈ A ∧ lvl v % k ≠ cs.val), weight i := by
      rw [← Finset.sum_filter_add_sum_filter_not (A.filter (fun x => x.1 = cs)) (fun x => lvl x.2 % k ≠ x.1.val)]
      have hz : ∑ x ∈ (A.filter (fun x => x.1 = cs)).filter (fun x => ¬ lvl x.2 % k ≠ x.1.val), w' x = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        simp only [Finset.mem_filter] at hx
        simp only [hw', if_neg hx.2]
      rw [hz, add_zero]
      apply Finset.sum_nbij' (fun x => x.2) (fun v => (cs, v))
      · intro x hx
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx ⊢
        obtain ⟨⟨hxA, hx1⟩, hx2⟩ := hx
        have : x = (cs, x.2) := Prod.ext hx1 rfl
        rw [← this]; exact ⟨hxA, by rw [← hx1]; exact hx2⟩
      · intro v hv
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hv ⊢
        simp_all
      · intro x hx
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at hx
        exact Prod.ext hx.1.2.symm rfl
      · intro v _; rfl
      · intro x hx
        simp only [Finset.mem_filter] at hx
        simp only [hw', if_pos hx.2]
    have h4 : ∑ a ∈ S, w' (⟨j, hj⟩, a) = ∑ i ∈ S, (if lvl i % k ≠ j then weight i else 0) := rfl
    rw [← h4]
    calc ∑ a ∈ S, w' (⟨j, hj⟩, a) ≤ _ := h1
      _ ≤ _ := h2
      _ = _ := h3
