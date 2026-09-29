-- Prove2me | solution 1 for TSPHeuristics.NearCheap.eq_4_11_tree_le_one_sub_inv_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:31:41.756521+00:00
-- url     : https://prove2.me/submissions/5974eae7-a028-4aab-876c-6adb52074563

import Mathlib
import Definitions.Def_TSPHeuristics_NearCheap_SpanningTree

open Classical


namespace TSPHeuristics.NearCheap

open TSPHeuristics.Shared Finset Fin.NatCast

lemma finval_add_one {N : ℕ} (i : Fin (N+1)) : (i+1).val = if i.val = N then 0 else i.val + 1 := by
  rw [Fin.val_add_one]
  by_cases h : i = Fin.last N
  · subst h; simp
  · rw [if_neg h, if_neg]; intro h'; exact h (Fin.ext (by simpa using h'))

lemma edgeLen_mk {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) (x y : Fin n) :
    edgeLen d s(x, y) = d x y := by
  simp [edgeLen, hd.symm y x]

theorem eq411_core {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : IsTSPDist d) :
    ∃ M : SimpleGraph (Fin n), M.IsTree ∧
      treeWeight d M ≤ (1 - 1 / (n : ℝ)) * optimal d := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    refine ⟨⊥, ⟨?_, SimpleGraph.isAcyclic_bot⟩, ?_⟩
    · rw [SimpleGraph.connected_iff]
      refine ⟨fun u v => ?_, inferInstance⟩
      have := u.isLt; have := v.isLt
      rw [show u = v from Fin.ext (by omega)]
    · have : treeWeight d (⊥ : SimpleGraph (Fin (0+1))) = 0 := by
        unfold treeWeight
        apply Finset.sum_eq_zero
        intro e he
        simp at he
      rw [this]; simp
  obtain ⟨τ, -, hτ⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Equiv.Perm (Fin (N+1))))
    (tourLength d)
  set w : Fin (N+1) → ℝ := fun k => d (τ k) (τ (k+1)) with hw
  have hopt : optimal d = ∑ k, w k := by
    unfold optimal; rw [hτ]; unfold tourLength
    apply Finset.sum_congr rfl; intro k _; simp [hw, finRotate_apply]
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ w Finset.univ_nonempty
  let e : Fin (N+1) → Sym2 (Fin (N+1)) := fun k => s(τ k, τ (k+1))
  let S : Finset (Sym2 (Fin (N+1))) := (Finset.univ.erase m).image e
  let M : SimpleGraph (Fin (N+1)) := SimpleGraph.fromEdgeSet (S : Set (Sym2 (Fin (N+1))))
  have hne : ∀ k : Fin (N+1), k ≠ k + 1 := by
    intro k h
    have := congrArg Fin.val h
    rw [finval_add_one] at this
    split_ifs at this <;> omega
  have hτne : ∀ k : Fin (N+1), τ k ≠ τ (k+1) := fun k h => hne k (τ.injective h)
  have hedge : ∀ x, x ∈ M.edgeSet ↔ x ∈ S := by
    intro x
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    constructor
    · intro h; exact h.1
    · intro h
      refine ⟨h, ?_⟩
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp h
      simp [e, hτne k]
  have hES : M.edgeSet = (S : Set _) := Set.ext hedge
  have hinj : Set.InjOn e ((Finset.univ.erase m : Finset (Fin (N+1))) : Set (Fin (N+1))) := by
    intro k hk k' hk' h
    simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_diff, Set.mem_univ,
      Set.mem_singleton_iff, true_and] at hk hk'
    simp only [e, Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact τ.injective h1
    · have h1 := congrArg Fin.val (τ.injective h1)
      have h2 := congrArg Fin.val (τ.injective h2)
      have hk1 := Fin.val_ne_iff.mpr hk
      have hk2 := Fin.val_ne_iff.mpr hk'
      have := k.isLt; have := k'.isLt; have := m.isLt
      rw [finval_add_one] at h1 h2
      apply Fin.ext
      split_ifs at h1 h2 <;> omega
  have hcard : S.card = N := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  -- connectivity
  let c : ℕ → Fin (N+1) := fun j => m + 1 + (j : Fin (N+1))
  have hc_ne : ∀ j, j < N → c j ≠ m := by
    intro j hj h
    have h' : (1 + (j : Fin (N+1))) = 0 := by
      have : m + (1 + (j : Fin (N+1))) = m + 0 := by rw [add_zero, ← add_assoc]; exact h
      exact add_left_cancel this
    have h'' : ((j + 1 : ℕ) : Fin (N+1)) = 0 := by
      simp only [Nat.cast_add, Nat.cast_one]; exact (add_comm _ _).trans h'
    have := congrArg Fin.val h''
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
    simp at this
  have hc_succ : ∀ j, c (j+1) = c j + 1 := by
    intro j; simp only [c, Nat.cast_add, Nat.cast_one, add_assoc]
  have hreach : ∀ j, j ≤ N → M.Reachable (τ (c 0)) (τ (c j)) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      refine (ih (by omega)).trans ?_
      apply SimpleGraph.Adj.reachable
      rw [hc_succ, SimpleGraph.fromEdgeSet_adj]
      refine ⟨?_, hτne _⟩
      simp only [S, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_erase]
      exact ⟨c j, ⟨hc_ne j (by omega), Finset.mem_univ _⟩, rfl⟩
  have hsurj : ∀ k : Fin (N+1), ∃ j, j ≤ N ∧ c j = k := by
    intro k
    refine ⟨(k - (m+1)).val, by have := (k - (m+1)).isLt; omega, ?_⟩
    simp only [c, Fin.cast_val_eq_self]
    abel
  have hconn : M.Connected := by
    rw [SimpleGraph.connected_iff]
    refine ⟨fun u v => ?_, inferInstance⟩
    obtain ⟨ju, hju, hu⟩ := hsurj (τ.symm u)
    obtain ⟨jv, hjv, hv⟩ := hsurj (τ.symm v)
    have h1 := hreach ju hju
    have h2 := hreach jv hjv
    rw [hu, Equiv.apply_symm_apply] at h1
    rw [hv, Equiv.apply_symm_apply] at h2
    exact h1.symm.trans h2
  refine ⟨M, ?_, ?_⟩
  · rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨hconn, ?_⟩
    rw [hES, Nat.card_coe_set_eq, Set.ncard_coe_finset, hcard]
    simp
  · unfold treeWeight
    trans ∑ e ∈ S, edgeLen d e
    · apply le_of_eq; apply Finset.sum_congr _ (fun _ _ => rfl)
      ext x; simp only [SimpleGraph.edgeFinset, Set.mem_toFinset]; exact hedge x
    rw [Finset.sum_image hinj]
    have h1 : ∑ x ∈ Finset.univ.erase m, edgeLen d (e x) = ∑ x ∈ Finset.univ.erase m, w x := by
      apply Finset.sum_congr rfl; intro k _; simp only [e, hw]; exact edgeLen_mk d hd _ _
    rw [h1, hopt]
    have h2 := Finset.sum_erase_add Finset.univ w (Finset.mem_univ m)
    have h3 : ∑ k, w k ≤ (N+1 : ℝ) * w m := by
      have := Finset.sum_le_card_nsmul Finset.univ w (w m) (fun k _ => hm k (Finset.mem_univ _))
      simpa using this
    have hpos : (0:ℝ) < N + 1 := by positivity
    push_cast
    have : (1 - 1 / ((N:ℝ) + 1)) * ∑ k, w k = ∑ k, w k - (∑ k, w k) / (N+1) := by
      field_simp
    rw [this]
    have : (∑ k, w k) / (N+1) ≤ w m := by rw [div_le_iff₀ hpos]; linarith
    linarith

end TSPHeuristics.NearCheap

open TSPHeuristics.NearCheap


theorem solution {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) :
    ∃ M : SimpleGraph (Fin n), M.IsTree ∧
      treeWeight d M ≤ (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d := by
  exact eq411_core hn d hd
