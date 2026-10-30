-- Prove2me | solution 1 for RendezvousKn.Sym.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T15:22:18.794799+00:00
-- url     : https://prove2.me/submissions/3c57ee6b-3b96-4925-b914-d07aec09327b

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model

namespace RdvCore

open RendezvousKn.Sym Finset

lemma card_perm_pos (n : ℕ) : (0:ℝ) < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
  exact_mod_cast Fintype.card_pos

lemma avgPerm_add (n : ℕ) (f g : Equiv.Perm (Fin n) → ℝ) :
    avgPerm n (fun π => f π + g π) = avgPerm n f + avgPerm n g := by
  unfold avgPerm; rw [Finset.sum_add_distrib, add_div]

lemma avgPerm_sub (n : ℕ) (f g : Equiv.Perm (Fin n) → ℝ) :
    avgPerm n (fun π => f π - g π) = avgPerm n f - avgPerm n g := by
  unfold avgPerm; rw [Finset.sum_sub_distrib, sub_div]

lemma avgPerm_sum {ι : Type*} (s : Finset ι) (n : ℕ) (f : ι → Equiv.Perm (Fin n) → ℝ) :
    avgPerm n (fun π => ∑ i ∈ s, f i π) = ∑ i ∈ s, avgPerm n (f i) := by
  unfold avgPerm; rw [Finset.sum_comm, Finset.sum_div]

lemma avgPerm_const_mul (n : ℕ) (c : ℝ) (f : Equiv.Perm (Fin n) → ℝ) :
    avgPerm n (fun π => c * f π) = c * avgPerm n f := by
  unfold avgPerm; rw [← Finset.mul_sum, mul_div_assoc]

lemma avgPerm_const (n : ℕ) (c : ℝ) : avgPerm n (fun _ => c) = c := by
  unfold avgPerm
  have := card_perm_pos n
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

lemma avgPerm_mono (n : ℕ) {f g : Equiv.Perm (Fin n) → ℝ} (h : ∀ π, f π ≤ g π) :
    avgPerm n f ≤ avgPerm n g := by
  unfold avgPerm
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun π _ => h π) (card_perm_pos n).le

lemma avgPerm_nonneg (n : ℕ) {f : Equiv.Perm (Fin n) → ℝ} (h : ∀ π, 0 ≤ f π) :
    0 ≤ avgPerm n f := by
  have := avgPerm_mono n (f := fun _ => 0) h
  rwa [avgPerm_const] at this

lemma avgPerm_mulLeft (n : ℕ) (σ : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin n) → ℝ) :
    avgPerm n (fun π => f (σ * π)) = avgPerm n f := by
  unfold avgPerm; congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft σ) _ _ (fun _ => rfl)

lemma prob_eval (n : ℕ) (i j : Fin n) :
    avgPerm n (fun π => if π i = j then 1 else 0) = 1 / n := by
  have hsame : ∀ j' : Fin n, avgPerm n (fun π => if π i = j' then (1:ℝ) else 0) =
      avgPerm n (fun π => if π i = j then 1 else 0) := by
    intro j'
    rw [← avgPerm_mulLeft n (Equiv.swap j j') (fun π => if π i = j' then (1:ℝ) else 0)]
    congr 1; funext π
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  have htot : ∑ j' : Fin n, avgPerm n (fun π => if π i = j' then (1:ℝ) else 0) = 1 := by
    rw [← avgPerm_sum]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact avgPerm_const n 1
  simp only [hsame, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htot
  have hn : (0:ℝ) < n := by exact_mod_cast (Fin.pos i)
  field_simp
  linarith

lemma waitTime_le {n : ℕ} (τA τB : Tactic n) (π : Equiv.Perm (Fin n)) :
    waitTime τA τB π ≤ n + 1 :=
  Finset.min'_le _ _ (mem_union_right _ (mem_singleton_self _))

lemma lt_waitTime_iff {n : ℕ} (τA τB : Tactic n) (π : Equiv.Perm (Fin n)) (k : ℕ)
    (hk : k ≤ n) :
    k < waitTime τA τB π ↔ ∀ i : Fin n, i.val < k → π (τA i) ≠ τB i := by
  unfold waitTime
  refine (Finset.lt_min'_iff _ _).trans ?_
  simp only [mem_union, mem_image, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h i hi heq
    have := h (i.val + 1) (Or.inl ⟨i, heq, rfl⟩)
    omega
  · rintro h y (⟨i, heq, rfl⟩ | rfl)
    · by_contra hc
      exact h i (by omega) heq
    · omega

lemma waitTime_eq_sum {n : ℕ} (τA τB : Tactic n) (π : Equiv.Perm (Fin n)) :
    (waitTime τA τB π : ℝ) =
      ∑ k ∈ range (n + 1), (if k < waitTime τA τB π then (1:ℝ) else 0) := by
  rw [Finset.sum_boole]
  have hle := waitTime_le τA τB π
  have : (range (n + 1)).filter (fun k => k < waitTime τA τB π) = range (waitTime τA τB π) := by
    ext k; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

lemma prob_lt_wait_ge {n : ℕ} (τA τB : Tactic n) (k : ℕ) (hk : k ≤ n) :
    1 - (k:ℝ) / n ≤ avgPerm n (fun π => if k < waitTime τA τB π then 1 else 0) ∧
      noRdvProb τA τB ≤ avgPerm n (fun π => if k < waitTime τA τB π then 1 else 0) := by
  constructor
  · have hpt : ∀ π : Equiv.Perm (Fin n),
        1 - ∑ i ∈ univ.filter (fun i : Fin n => i.val < k),
          (if π (τA i) = τB i then (1:ℝ) else 0) ≤
        (if k < waitTime τA τB π then 1 else 0) := by
      intro π
      by_cases h : ∀ i : Fin n, i.val < k → π (τA i) ≠ τB i
      · rw [if_pos ((lt_waitTime_iff τA τB π k hk).2 h)]
        have : ∑ i ∈ univ.filter (fun i : Fin n => i.val < k),
            (if π (τA i) = τB i then (1:ℝ) else 0) = 0 := by
          apply Finset.sum_eq_zero; intro i hi
          simp only [mem_filter, mem_univ, true_and] at hi
          rw [if_neg (h i hi)]
        linarith
      · push Not at h
        obtain ⟨i, hi, heq⟩ := h
        have h1 : (1:ℝ) ≤ ∑ i ∈ univ.filter (fun i : Fin n => i.val < k),
            (if π (τA i) = τB i then (1:ℝ) else 0) := by
          have := Finset.single_le_sum (f := fun i => if π (τA i) = τB i then (1:ℝ) else 0)
            (fun j _ => by positivity) (show i ∈ univ.filter (fun i : Fin n => i.val < k) by
              simp [hi])
          simpa [heq] using this
        have h2 : (0:ℝ) ≤ (if k < waitTime τA τB π then 1 else 0) := by positivity
        linarith
    have := avgPerm_mono n hpt
    rw [avgPerm_sub, avgPerm_const, avgPerm_sum] at this
    simp only [prob_eval, Finset.sum_const, Fin.card_filter_val_lt, nsmul_eq_mul,
      min_eq_right hk] at this
    convert this using 2
    ring
  · unfold noRdvProb
    apply avgPerm_mono; intro π
    split_ifs with h1 h2 <;> try norm_num
    exact h2 ((lt_waitTime_iff τA τB π k hk).2 fun i _ => h1 i)

lemma W_eq_sum {n : ℕ} (τA τB : Tactic n) :
    W τA τB = ∑ k ∈ range (n + 1),
      avgPerm n (fun π => if k < waitTime τA τB π then (1:ℝ) else 0) := by
  unfold W
  simp only [waitTime_eq_sum]
  rw [avgPerm_sum]

lemma W_ge (n : ℕ) (τA τB : Tactic n) : ((n:ℝ) + 1) / 2 ≤ W τA τB := by
  rw [W_eq_sum]
  have h : ∑ k ∈ range (n + 1), (1 - (k:ℝ) / n) ≤ ∑ k ∈ range (n + 1),
      avgPerm n (fun π => if k < waitTime τA τB π then (1:ℝ) else 0) :=
    Finset.sum_le_sum fun k hk => (prob_lt_wait_ge τA τB k (by
      simp at hk; omega)).1
  refine le_trans ?_ h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have hnR : (0:ℝ) < n := by exact_mod_cast hn
    rw [Finset.sum_sub_distrib, ← Finset.sum_div]
    have hs : ∑ k ∈ range (n + 1), (k:ℝ) = n * (n + 1) / 2 := by
      have := Finset.sum_range_id_mul_two (n + 1)
      simp only [Nat.add_sub_cancel] at this
      have h' : ((∑ k ∈ range (n + 1), k : ℕ) : ℝ) * 2 = ((n + 1) * n : ℕ) := by
        exact_mod_cast this
      push_cast at h'
      linarith
    rw [hs]; simp
    field_simp
    ring_nf; nlinarith

end RdvCore

open RendezvousKn.Sym

theorem solution (n : ℕ) (σA σB : Tactic n → ℝ)
    (hσA : σA ∈ stdSimplex ℝ (Tactic n)) (hσB : σB ∈ stdSimplex ℝ (Tactic n)) :
    ((n : ℝ) + 1) / 2 ≤ expWait σA σB := by
  obtain ⟨hA0, hA1⟩ := hσA
  obtain ⟨hB0, hB1⟩ := hσB
  have key : ∑ a : Tactic n, ∑ b : Tactic n, σA a * σB b * (((n : ℝ) + 1) / 2) ≤
      expWait σA σB := by
    unfold expWait
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    exact mul_le_mul_of_nonneg_left (RdvCore.W_ge n a b) (mul_nonneg (hA0 a) (hB0 b))
  have e : ∑ a : Tactic n, ∑ b : Tactic n, σA a * σB b * (((n : ℝ) + 1) / 2) =
      ((n : ℝ) + 1) / 2 := by
    simp only [← Finset.sum_mul, ← Finset.mul_sum, hB1, hA1]
    ring
  linarith
