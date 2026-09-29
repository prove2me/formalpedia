-- Prove2me | solution 1 for TSPHeuristics.NNLower.optimal_gbar
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:13:00.978362+00:00
-- url     : https://prove2.me/submissions/a4e6fa42-56ae-41b2-95ec-1fdbba7a229f

import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_TSPModel
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

lemma aux_og_ell_ge (j : ℕ) (hj : 1 ≤ j) : 2 ≤ ell j := by
  unfold ell
  rcases neg_one_pow_eq_or ℝ j with h | h
  · rw [h]
    have hj1 : j ≠ 1 := by
      intro h1; subst h1; norm_num at h
    have h4 : (4:ℝ) ≤ 2 ^ j := by
      have : 2 ≤ j := by omega
      calc (4:ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) this
    rw [le_div_iff₀ (by norm_num)]; linarith
  · rw [h]
    have h2 : (2:ℝ) ≤ 2 ^ j := by
      calc (2:ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
    rw [le_div_iff₀ (by norm_num)]; linarith

lemma aux_og_weightF (j : ℕ) : ∀ e ∈ edgesF (j + 1), (1:ℝ) ≤ e.2.2 := by
  induction j with
  | zero =>
    intro e he
    simp [edgesF] at he
    rcases he with rfl | rfl | rfl <;> norm_num
  | succ j ih =>
    intro e he
    have hl := aux_og_ell_ge (j + 1) (by omega)
    rw [edgesF] at he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil] at he
    rcases he with (he | ⟨e', he', rfl⟩) | he
    · exact ih e he
    · exact ih e' he'
    · rcases he with rfl | rfl | rfl | rfl | h
      · norm_num
      · norm_num
      · simp only; linarith
      · simp only; linarith
      · exact h.elim

lemma aux_og_numNodes_succ (j : ℕ) : numNodes (j + 1 + 1) = 2 * numNodes (j + 1) + 1 := by
  simp only [numNodes]
  rw [pow_succ 2 (j + 1 + 1)]
  have := Nat.one_le_two_pow (n := j + 1 + 1)
  omega

lemma aux_og_consec (j : ℕ) :
    ∀ k, k + 1 < numNodes (j + 1) → (k, k + 1, (1:ℝ)) ∈ edgesF (j + 1) := by
  induction j with
  | zero =>
    intro k hk
    have h3 : numNodes (0 + 1) = 3 := rfl
    have hk' : k < 2 := by omega
    interval_cases k <;> simp [edgesF]
  | succ j ih =>
    intro k hk
    rw [aux_og_numNodes_succ] at hk
    rw [edgesF]
    simp only [List.mem_append, List.mem_map, List.mem_cons]
    have hs1 : 1 ≤ numNodes (j + 1) := by
      simp only [numNodes]
      have : 2 ≤ 2 ^ (j + 1 + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rcases lt_trichotomy (k + 1) (numNodes (j + 1)) with h | h | h
    · left; left; exact ih k h
    · right; left
      have : k = numNodes (j + 1) - 1 := by omega
      subst this
      rw [h]
    · rcases Nat.lt_or_ge k (numNodes (j + 1) + 1) with h2 | h2
      · have : k = numNodes (j + 1) := by omega
        subst this
        right; right; left; trivial
      · left; right
        refine ⟨(k - (numNodes (j + 1) + 1), k - (numNodes (j + 1) + 1) + 1, 1), ?_, ?_⟩
        · exact ih _ (by omega)
        · simp only [Prod.mk.injEq]
          refine ⟨by omega, by omega, trivial⟩

lemma aux_og_walk_nonneg {E : List (ℕ × ℕ × ℝ)} (hE : ∀ e ∈ E, (1:ℝ) ≤ e.2.2) {x y : ℕ}
    {c : ℝ} (h : WalkCost E x y c) : 0 ≤ c ∧ (x ≠ y → 1 ≤ c) := by
  induction h with
  | nil x => simp
  | cons he h ih =>
    rename_i x y z w c
    have hw : 1 ≤ w := by
      rcases he with he | he
      · exact hE _ he
      · exact hE _ he
    constructor
    · linarith [ih.1]
    · intro _; linarith [ih.1]

lemma aux_og_walk_path {E : List (ℕ × ℕ × ℝ)} {n : ℕ}
    (hE : ∀ k, k + 1 < n → (k, k + 1, (1:ℝ)) ∈ E) :
    ∀ m a, a + m < n → WalkCost E a (a + m) m ∧ WalkCost E (a + m) a m := by
  intro m
  induction m with
  | zero =>
    intro a _
    simp only [Nat.add_zero, Nat.cast_zero]
    exact ⟨WalkCost.nil a, WalkCost.nil a⟩
  | succ m ih =>
    intro a ha
    constructor
    · have h1 := (ih (a + 1) (by omega)).1
      have h2 := WalkCost.cons (E := E) (x := a) (w := 1) (Or.inl (hE a (by omega))) h1
      rw [show a + 1 + m = a + (m + 1) by omega] at h2
      convert h2 using 1
      push_cast; ring
    · have h1 := (ih a (by omega)).2
      have he : (a + m, a + (m + 1), (1:ℝ)) ∈ E := by
        have := hE (a + m) (by omega)
        rwa [show a + m + 1 = a + (m + 1) by omega] at this
      have h2 := WalkCost.cons (E := E) (x := a + (m + 1)) (y := a + m) (w := 1) (Or.inr he) h1
      convert h2 using 1
      push_cast; ring

lemma aux_og_opt {n : ℕ} (hn : 2 ≤ n) (d : Fin n → Fin n → ℝ)
    (hlow : ∀ a b : Fin n, a ≠ b → 1 ≤ d a b)
    (hup : ∀ a b : Fin n, ((b : ℕ) = a + 1 ∨ ((a : ℕ) + 1 = n ∧ (b : ℕ) = 0)) → d a b ≤ 1) :
    optimal d = n := by
  apply le_antisymm
  · unfold optimal
    refine (Finset.inf'_le _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))).trans ?_
    unfold tourLength
    calc ∑ k, d ((1 : Equiv.Perm (Fin n)) k) ((1 : Equiv.Perm (Fin n)) (finRotate n k))
        ≤ ∑ _k : Fin n, (1:ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          simp only [Equiv.Perm.coe_one, id]
          apply hup
          obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
          rw [coe_finRotate]
          split_ifs with h
          · right
            subst h
            simp
          · left; rfl
      _ = n := by simp
  · unfold optimal
    apply Finset.le_inf'
    intro τ _
    unfold tourLength
    calc (n:ℝ) = ∑ _k : Fin n, (1:ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k _
        apply hlow
        intro h
        have h' := τ.injective h
        have hs := support_finRotate_of_le hn
        have : k ∈ (finRotate n).support := by rw [hs]; exact Finset.mem_univ _
        exact (Equiv.Perm.mem_support.mp this) h'.symm

theorem aux_og_main (j : ℕ) : optimal (gbar (j + 1)) = (numNodes (j + 1) : ℝ) := by
  have hE : ∀ e ∈ edgesG (j + 1), (1:ℝ) ≤ e.2.2 := by
    intro e he
    unfold edgesG at he
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil] at he
    rcases he with he | rfl | rfl | h
    · exact aux_og_weightF j e he
    · norm_num
    · have := aux_og_ell_ge (j + 1) (by omega)
      simp only; linarith
    · exact h.elim
  have hC : ∀ k, k + 1 < numNodes (j + 1) → (k, k + 1, (1:ℝ)) ∈ edgesG (j + 1) := by
    intro k hk
    unfold edgesG
    exact List.mem_append_left _ (aux_og_consec j k hk)
  have hn : 2 ≤ numNodes (j + 1) := by
    simp only [numNodes]
    have : 4 ≤ 2 ^ (j + 1 + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  apply aux_og_opt hn
  · intro a b hab
    unfold gbar spDist
    apply le_csInf
    · -- nonempty: a walk exists
      rcases le_total (a : ℕ) (b : ℕ) with h | h
      · obtain ⟨m, hm⟩ : ∃ m, (b : ℕ) = a + m := ⟨b - a, by omega⟩
        refine ⟨m, ?_⟩
        have := (aux_og_walk_path hC m a (by omega)).1
        rw [← hm] at this
        exact this
      · obtain ⟨m, hm⟩ : ∃ m, (a : ℕ) = b + m := ⟨a - b, by omega⟩
        refine ⟨m, ?_⟩
        have := (aux_og_walk_path hC m b (by omega)).2
        rw [← hm] at this
        exact this
    · rintro c hc
      exact (aux_og_walk_nonneg hE hc).2 (fun h => hab (Fin.ext h))
  · intro a b hab
    unfold gbar spDist
    apply csInf_le ⟨0, fun c hc => (aux_og_walk_nonneg hE hc).1⟩
    show WalkCost (edgesG (j + 1)) a b 1
    have key : WalkCost (edgesG (j + 1)) a b (1 + 0) := by
      refine WalkCost.cons ?_ (WalkCost.nil _)
      rcases hab with h | ⟨h1, h2⟩
      · left; rw [h]; exact hC a (by omega)
      · right; rw [h2]
        unfold edgesG
        apply List.mem_append_right
        simp only [List.mem_cons]
        left
        have : (a : ℕ) = numNodes (j + 1) - 1 := by omega
        rw [this]
    simpa using key

end TSPHeuristics.NNLower

open TSPHeuristics.NNLower

theorem solution (i : ℕ) (hi : 1 ≤ i) :
    optimal (gbar i) = (2 : ℝ) ^ (i + 1) - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [aux_og_main j]
  simp only [numNodes]
  rw [Nat.cast_sub (Nat.one_le_two_pow)]
  push_cast
  ring
