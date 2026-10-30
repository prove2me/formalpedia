-- Prove2me | solution 1 for RendezvousKn.Sym.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T15:23:38.811062+00:00
-- url     : https://prove2.me/submissions/375dc960-7b33-46c9-b62d-e4425454eb64

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

namespace RdvCore
open RendezvousKn.Sym Finset

lemma noRdvProb_le_one {n : ℕ} (τA τB : Tactic n) : noRdvProb τA τB ≤ 1 := by
  unfold noRdvProb
  calc _ ≤ avgPerm n (fun _ => (1:ℝ)) := avgPerm_mono n (fun π => by split_ifs <;> norm_num)
    _ = 1 := avgPerm_const n 1

lemma ramp_sum (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ((n:ℝ) + 1) / 2 + β ^ 2 / 2 * n ≤ ∑ k ∈ range (n + 1), max (1 - (k:ℝ) / n) β := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  set g : ℕ → ℝ := fun j => max 0 (β - (j:ℝ) / n)
  have hterm : ∀ k ∈ range (n + 1), (1 - (k:ℝ) / n) + g (n - k) ≤ max (1 - (k:ℝ) / n) β := by
    intro k hk
    simp only [mem_range] at hk
    simp only [g]
    rw [Nat.cast_sub (by omega)]
    rcases le_total 0 (β - ((n:ℝ) - k) / n) with h | h
    · rw [max_eq_right h]
      have : 1 - (k:ℝ) / n + (β - ((n:ℝ) - k) / n) = β := by field_simp; ring
      rw [this]; exact le_max_right _ _
    · rw [max_eq_left h]; simp
  have h1 := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at h1
  have hrefl : ∑ k ∈ range (n + 1), g (n - k) = ∑ j ∈ range (n + 1), g j := by
    have := Finset.sum_range_reflect g (n + 1)
    simpa using this
  rw [hrefl] at h1
  -- the linear part
  have hs : ∑ k ∈ range (n + 1), (k:ℝ) = n * (n + 1) / 2 := by
    have := Finset.sum_range_id_mul_two (n + 1)
    simp only [Nat.add_sub_cancel] at this
    have h' : ((∑ k ∈ range (n + 1), k : ℕ) : ℝ) * 2 = ((n + 1) * n : ℕ) := by
      exact_mod_cast this
    push_cast at h'
    linarith
  have hlin : ∑ k ∈ range (n + 1), (1 - (k:ℝ) / n) = ((n:ℝ) + 1) / 2 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hs]; simp
    field_simp; ring
  rw [hlin] at h1
  -- the ramp part
  set J : ℕ := ⌊β * n⌋₊
  have hJx : (J:ℝ) ≤ β * n := Nat.floor_le (by positivity)
  have hxJ : β * n < J + 1 := Nat.lt_floor_add_one _
  have hJn : J ≤ n := by
    have : (J:ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hsub : ∑ j ∈ range (J + 1), g j ≤ ∑ j ∈ range (n + 1), g j :=
    Finset.sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
      (fun j _ _ => le_max_left _ _)
  have hlow : ∑ j ∈ range (J + 1), (β - (j:ℝ) / n) ≤ ∑ j ∈ range (J + 1), g j :=
    Finset.sum_le_sum fun j _ => le_max_right _ _
  have hsJ : ∑ j ∈ range (J + 1), (j:ℝ) = J * (J + 1) / 2 := by
    have := Finset.sum_range_id_mul_two (J + 1)
    simp only [Nat.add_sub_cancel] at this
    have h' : ((∑ k ∈ range (J + 1), k : ℕ) : ℝ) * 2 = ((J + 1) * J : ℕ) := by
      exact_mod_cast this
    push_cast at h'
    linarith
  have hcomp : ∑ j ∈ range (J + 1), (β - (j:ℝ) / n) = (J + 1) * β - J * (J + 1) / (2 * n) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsJ]; simp
    field_simp
  have hquad : β ^ 2 / 2 * n ≤ (J + 1) * β - J * (J + 1) / (2 * n) := by
    have key : (β * n) ^ 2 ≤ 2 * (J + 1) * (β * n) - J * (J + 1) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hJx) (sub_nonneg.2 hxJ.le)]
    have e : (J + 1) * β - J * (J + 1) / (2 * n) =
        (2 * (J + 1) * (β * n) - J * (J + 1)) / (2 * n) := by field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have : β ^ 2 / 2 * n * (2 * n) = (β * n) ^ 2 := by ring
    linarith
  linarith

lemma W_ge_ramp (n : ℕ) (hn : 0 < n) (τA τB : Tactic n) (β : ℝ) (hβ : 0 ≤ β)
    (hprob : β ≤ noRdvProb τA τB) :
    ((n:ℝ) + 1) / 2 + β ^ 2 / 2 * n ≤ W τA τB := by
  rw [W_eq_sum]
  refine le_trans (ramp_sum n hn β hβ (hprob.trans (noRdvProb_le_one τA τB))) ?_
  apply Finset.sum_le_sum; intro k hk
  simp only [mem_range] at hk
  have := prob_lt_wait_ge τA τB k (by omega)
  exact max_le this.1 (hprob.trans this.2)

end RdvCore

open RendezvousKn.Sym

theorem solution (n : ℕ) (hn : 2 ≤ n) (τA τB : Tactic n) (β : ℝ) (hβ : 0 < β)
    (hprob : β ≤ noRdvProb τA τB) :
    ((n : ℝ) + 1) / 2 + β ^ 2 / 2 * n ≤ W τA τB :=
  RdvCore.W_ge_ramp n (by omega) τA τB β hβ.le hprob
