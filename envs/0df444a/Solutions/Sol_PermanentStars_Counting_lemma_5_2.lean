-- Prove2me | solution 1 for PermanentStars.Counting.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T18:44:33.088505+00:00
-- url     : https://prove2.me/submissions/d354329f-0cc0-429d-89f2-91ea5aa4ec95

import Definitions.Def_PermanentStars_Counting_Partitions


open scoped BigOperators

namespace PermanentStars.Counting.PrefixProof

lemma prefix_le {N : ℕ} (S : Finset (Fin N)) : prefixLength S ≤ N := by
  unfold prefixLength
  apply Finset.sup_le
  intro p hp
  exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)

lemma prefix_mem {N : ℕ} (S : Finset (Fin N)) (i : Fin N) (hi : i.val < prefixLength S) : i ∈ S := by
  by_contra hnot
  have hle : prefixLength S ≤ i.val := by
    apply Finset.sup_le
    intro p hp
    have hh := (Finset.mem_filter.mp hp).2
    by_contra h
    exact hnot (hh i (Nat.lt_of_not_ge h))
  omega

def before (N p : ℕ) : Finset (Fin N) := Finset.univ.filter (fun i => i.val < p)

lemma before_card {N p : ℕ} (hp : p ≤ N) : (before N p).card = p := by
  simpa only [before, Fin.card_filter_val_lt, min_eq_right hp]

lemma before_subset {N : ℕ} (S : Finset (Fin N)) : before N (prefixLength S) ⊆ S := by
  intro i hi
  exact prefix_mem S i (Finset.mem_filter.mp hi).2

lemma sdiff_injective {α : Type*} [DecidableEq α] (P : Finset α) :
    Set.InjOn (fun S : Finset α => S \ P) {S | P ⊆ S} := by
  intro A hA B hB he
  have ha : P ∪ (A \ P) = A := Finset.union_sdiff_of_subset hA
  have hb : P ∪ (B \ P) = B := Finset.union_sdiff_of_subset hB
  exact ha.symm.trans ((congrArg (fun T => P ∪ T) he).trans hb)

lemma weighted_small_sets {α : Type*} [DecidableEq α] (s : Finset α)
    (F : Finset (Finset α)) (hF : ∀ T ∈ F, T ⊆ s) (L : ℕ)
    (hL : ∀ T ∈ F, T.card ≤ L) (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    (F.card : ℝ) * x ^ L ≤ (x + 1) ^ s.card := by
  calc
    _ = ∑ T ∈ F, x ^ L := by simp
    _ ≤ ∑ T ∈ F, x ^ T.card := by
      apply Finset.sum_le_sum
      intro T hT
      exact pow_le_pow_of_le_one hx.le hx1 (hL T hT)
    _ ≤ ∑ T ∈ s.powerset, x ^ T.card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro T hT
        exact Finset.mem_powerset.mpr (hF T hT)
      · intro T _ _
        positivity
    _ = (x + 1) ^ s.card := by
      simpa only [one_pow, mul_one] using Finset.sum_pow_mul_eq_add_pow x 1 s

lemma prefix_fiber_bound (N r p : ℕ) (hr : 1 ≤ r) (hp : p ≤ N)
    (c : ℝ) (hc : 1 < c) (hc2 : c < 2) (hprod : 1 ≤ c * (c - 1) ^ (r - 1)) :
    (((Finset.univ : Finset (Finset (Fin N))).filter
      (fun S => S.card ≤ r * prefixLength S ∧ prefixLength S = p)).card : ℝ) ≤ c ^ N := by
  classical
  let P := before N p
  let A := (Finset.univ : Finset (Finset (Fin N))).filter
    (fun S => S.card ≤ r * prefixLength S ∧ prefixLength S = p)
  let F := A.image (fun S => S \ P)
  have hP (S : Finset (Fin N)) (hS : S ∈ A) : P ⊆ S := by
    have he := (Finset.mem_filter.mp hS).2.2
    simpa only [P, ← he] using before_subset S
  have hcard : F.card = A.card := Finset.card_image_of_injOn (by
    intro S hS T hT he
    exact sdiff_injective P (hP S hS) (hP T hT) he)
  have hsub : ∀ T ∈ F, T ⊆ Finset.univ \ P := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
    exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _)
  have hL : ∀ T ∈ F, T.card ≤ (r - 1) * p := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
    have hsize := (Finset.mem_filter.mp hS).2.1
    have he := (Finset.mem_filter.mp hS).2.2
    rw [he] at hsize
    have hpart := Finset.card_sdiff_add_card_eq_card (hP S hS)
    have hpc : P.card = p := before_card hp
    rw [hpc] at hpart
    have hrp : r * p = (r - 1) * p + p := by
      calc
        _ = ((r - 1) + 1) * p := congrArg (fun x => x * p) (Nat.sub_add_cancel hr).symm
        _ = _ := by ring
    omega
  have hcomp : (Finset.univ \ P).card = N - p := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    rw [show P.card = p from before_card hp]
  have hw := weighted_small_sets (Finset.univ \ P) F hsub ((r - 1) * p) hL
    (c - 1) (by linarith) (by linarith)
  rw [hcard, hcomp, sub_add_cancel] at hw
  have hpow : (c - 1) ^ ((r - 1) * p) = ((c - 1) ^ (r - 1)) ^ p := pow_mul _ _ _
  have hcp : 1 ≤ c ^ p * (c - 1) ^ ((r - 1) * p) := by
    rw [hpow, ← mul_pow]
    exact one_le_pow₀ hprod
  have hpositive : 0 < (c - 1) ^ ((r - 1) * p) := pow_pos (by linarith) _
  have hnonneg : 0 ≤ c ^ (N - p) := (pow_pos (by linarith) _).le
  have hbound : c ^ (N - p) ≤ c ^ N * (c - 1) ^ ((r - 1) * p) := by
    calc
      _ ≤ c ^ (N - p) * (c ^ p * (c - 1) ^ ((r - 1) * p)) :=
        le_mul_of_one_le_right hnonneg hcp
      _ = _ := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hp]
  exact (mul_le_mul_iff_left₀ hpositive).mp (hw.trans hbound)

theorem lemma_5_2 (N r : ℕ) (hr : 1 ≤ r) (c : ℝ)
    (hc : 1 < c) (hc2 : c < 2) (hprod : 1 ≤ c * (c - 1) ^ (r - 1)) :
    (prefixCount N r : ℝ) ≤ (N + 1 : ℝ) * c ^ N := by
  classical
  let A := (Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card ≤ r * prefixLength S)
  have hsum : (∑ p ∈ Finset.range (N + 1), (A.filter fun S => prefixLength S = p).card) = A.card := by
    symm
    apply Finset.card_eq_sum_card_fiberwise
    intro S hS
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (prefix_le S))
  calc
    _ = ∑ p ∈ Finset.range (N + 1), ((A.filter fun S => prefixLength S = p).card : ℝ) := by
      exact_mod_cast hsum.symm
    _ ≤ ∑ p ∈ Finset.range (N + 1), c ^ N := by
      apply Finset.sum_le_sum
      intro p hp
      have he : A.filter (fun S => prefixLength S = p) =
          Finset.univ.filter (fun S => S.card ≤ r * prefixLength S ∧ prefixLength S = p) := by
        ext S
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [he]
      exact prefix_fiber_bound N r p hr (Nat.le_of_lt_succ (Finset.mem_range.mp hp)) c hc hc2 hprod
    _ = _ := by simp [Nat.cast_add, Nat.cast_one]

end PermanentStars.Counting.PrefixProof

open PermanentStars.Counting

theorem solution (N r : ℕ) (hr : 1 ≤ r) (c : ℝ)
    (hc : 1 < c) (hc2 : c < 2) (hprod : 1 ≤ c * (c - 1) ^ (r - 1)) :
    (prefixCount N r : ℝ) ≤ (N + 1 : ℝ) * c ^ N  := PermanentStars.Counting.PrefixProof.lemma_5_2 N r hr c hc hc2 hprod
