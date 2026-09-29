-- Prove2me | solution 1 for Transcendence.exists_modByMonic_length_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T16:47:01.392178+00:00
-- url     : https://prove2.me/submissions/c575b504-2357-40b1-bfe7-c4e772c11fff

import Mathlib
import Theorems.Thm_Transcendence_length_sum_le
import Theorems.Thm_Transcendence_length_mul_le

/-!
# Remainders modulo a monic polynomial in `ℤ[X][Y]`

The length of `P ∈ ℤ[X][Y]` is the sum of the absolute values of all its integer coefficients.
It is subadditive and submultiplicative.

Let `Q` be monic in `Y` of degree `d ≥ 1`, and write `R_k = Yᵏ %ₘ Q`. Then `R_0 = 1` and
`R_{k+1} = Y R_k - c_k Q`, where `c_k ∈ ℤ[X]` is the coefficient of `Y^(d-1)` in `R_k`: the
right side is congruent to `Y^(k+1)` modulo `Q` and has `Y`-degree below `d`. Since `c_k` is a
coefficient of `R_k`, `len R_{k+1} ≤ len R_k + len R_k · len Q`, so `len R_k ≤ (1 + len Q)ᵏ`,
and the `X`-degrees of the coefficients of `R_k` are at most `k D`, where `D` bounds the
`X`-degrees of the coefficients of `Q`. Division by a monic polynomial is linear, so
`P %ₘ Q = ∑ₖ Pₖ R_k`, and the bounds follow with `C = 1 + len Q + D`.

If `Q` is monic of degree `0`, then `Q = 1` and every remainder is `0`; if `Q` is not monic,
then `P %ₘ Q = P`. In both cases `C = 1` works.

In the code, `Y` is the variable `X` of the outer ring `ℤ[X][Y]`, and `X` is `C X`.
-/

namespace S7W3_exists_modByMonic_length_le

open Polynomial

/-- The length of a polynomial in `ℤ[X]`: the sum of the absolute values of its coefficients. -/
noncomputable def len1 (p : Polynomial ℤ) : ℕ :=
  ∑ i ∈ p.support, (p.coeff i).natAbs

/-- The length of a polynomial in `ℤ[X][Y]`: the sum of the lengths of its coefficients. -/
noncomputable def len (P : Polynomial (Polynomial ℤ)) : ℕ :=
  ∑ k ∈ P.support, len1 (P.coeff k)

theorem len_mul_le (P R : Polynomial (Polynomial ℤ)) : len (P * R) ≤ len P * len R :=
  Transcendence.length_mul_le P R

theorem len_sum_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial (Polynomial ℤ)) :
    len (∑ i ∈ s, f i) ≤ ∑ i ∈ s, len (f i) :=
  Transcendence.length_sum_le s f

theorem len1_zero : len1 0 = 0 := by
  simp only [len1, support_zero, Finset.sum_empty]

theorem len_zero : len 0 = 0 := by
  simp only [len, support_zero, Finset.sum_empty]

theorem len1_eq_sum (p : Polynomial ℤ) {s : Finset ℕ} (hs : p.support ⊆ s) :
    len1 p = ∑ i ∈ s, (p.coeff i).natAbs := by
  refine Finset.sum_subset hs fun i _ hi => ?_
  rw [notMem_support_iff.mp hi, Int.natAbs_zero]

theorem len_eq_sum (P : Polynomial (Polynomial ℤ)) {s : Finset ℕ} (hs : P.support ⊆ s) :
    len P = ∑ k ∈ s, len1 (P.coeff k) := by
  refine Finset.sum_subset hs fun k _ hk => ?_
  rw [notMem_support_iff.mp hk, len1_zero]

/-- A single coefficient is no longer than the whole polynomial. -/
theorem len1_coeff_le (P : Polynomial (Polynomial ℤ)) (k : ℕ) : len1 (P.coeff k) ≤ len P := by
  by_cases hk : k ∈ P.support
  · exact Finset.single_le_sum (f := fun j => len1 (P.coeff j)) (fun _ _ => Nat.zero_le _) hk
  · rw [notMem_support_iff.mp hk, len1_zero]
    exact Nat.zero_le _

theorem len1_one : len1 1 = 1 := by
  have hs : (1 : Polynomial ℤ).support ⊆ {0} := by
    rw [← C_1]
    exact support_C_subset 1
  rw [len1_eq_sum 1 hs, Finset.sum_singleton, coeff_one_zero, Int.natAbs_one]

theorem len_C (p : Polynomial ℤ) : len (C p) = len1 p := by
  rw [len_eq_sum (C p) (support_C_subset p), Finset.sum_singleton, coeff_C_zero]

theorem len_one : len 1 = 1 := by
  rw [← C_1, len_C, len1_one]

theorem len_X : len (X : Polynomial (Polynomial ℤ)) = 1 := by
  have hs : (X : Polynomial (Polynomial ℤ)).support ⊆ {1} := fun i hi => by
    rwa [support_X] at hi
  rw [len_eq_sum X hs, Finset.sum_singleton, coeff_X_one, len1_one]

theorem len_add_le (A B : Polynomial (Polynomial ℤ)) : len (A + B) ≤ len A + len B := by
  have h := len_sum_le Finset.univ (fun b : Bool => cond b A B)
  rw [Fintype.sum_bool, Fintype.sum_bool] at h
  exact h

theorem len_neg (A : Polynomial (Polynomial ℤ)) : len (-A) = len A := by
  unfold len len1
  rw [support_neg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_neg, support_neg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_neg, Int.natAbs_neg]

theorem len_sub_le (A B : Polynomial (Polynomial ℤ)) : len (A - B) ≤ len A + len B := by
  rw [sub_eq_add_neg, ← len_neg B]
  exact len_add_le A (-B)

/-! ### `X`-degrees of the coefficients -/

theorem degX_mul {A B : Polynomial (Polynomial ℤ)} {a b : ℕ}
    (hA : ∀ k, (A.coeff k).natDegree ≤ a) (hB : ∀ k, (B.coeff k).natDegree ≤ b) (k : ℕ) :
    ((A * B).coeff k).natDegree ≤ a + b := by
  rw [coeff_mul]
  refine natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
  exact natDegree_mul_le.trans (Nat.add_le_add (hA x.1) (hB x.2))

theorem degX_sub {A B : Polynomial (Polynomial ℤ)} {a : ℕ}
    (hA : ∀ k, (A.coeff k).natDegree ≤ a) (hB : ∀ k, (B.coeff k).natDegree ≤ a) (k : ℕ) :
    ((A - B).coeff k).natDegree ≤ a := by
  rw [coeff_sub]
  exact (natDegree_sub_le _ _).trans (max_le (hA k) (hB k))

theorem degX_X (k : ℕ) : ((X : Polynomial (Polynomial ℤ)).coeff k).natDegree ≤ 0 := by
  rw [coeff_X]
  split_ifs
  · rw [natDegree_one]
  · rw [natDegree_zero]

theorem degX_C (p : Polynomial ℤ) (k : ℕ) : ((C p).coeff k).natDegree ≤ p.natDegree := by
  rw [coeff_C]
  split_ifs
  · exact le_rfl
  · rw [natDegree_zero]
    exact Nat.zero_le _

/-- A bound for the `X`-degrees of the coefficients of `Q`. -/
noncomputable def degXQ (Q : Polynomial (Polynomial ℤ)) : ℕ :=
  ∑ k ∈ Q.support, (Q.coeff k).natDegree

theorem natDegree_coeff_le_degXQ (Q : Polynomial (Polynomial ℤ)) (j : ℕ) :
    (Q.coeff j).natDegree ≤ degXQ Q := by
  by_cases hj : j ∈ Q.support
  · exact Finset.single_le_sum (f := fun k => (Q.coeff k).natDegree) (fun _ _ => Nat.zero_le _) hj
  · rw [notMem_support_iff.mp hj, natDegree_zero]
    exact Nat.zero_le _

/-! ### Reducing the powers of `Y` -/

/-- One reduction step: `Y^(k+1) %ₘ Q = Y (Yᵏ %ₘ Q) - c Q`, with `c` the coefficient of
`Y^(d-1)` in `Yᵏ %ₘ Q`. -/
theorem X_pow_succ_modByMonic {Q : Polynomial (Polynomial ℤ)} (hQ : Q.Monic)
    (hd : 1 ≤ Q.natDegree) (k : ℕ) :
    X ^ (k + 1) %ₘ Q = X * (X ^ k %ₘ Q) - C ((X ^ k %ₘ Q).coeff (Q.natDegree - 1)) * Q := by
  have hQ1 : Q ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hd
    omega
  have hR : (X ^ k %ₘ Q).natDegree < Q.natDegree := natDegree_modByMonic_lt _ hQ hQ1
  have hle : (X * (X ^ k %ₘ Q) - C ((X ^ k %ₘ Q).coeff (Q.natDegree - 1)) * Q).natDegree
      ≤ Q.natDegree - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [coeff_sub, coeff_X_mul, coeff_C_mul]
    rcases Nat.lt_or_ge Q.natDegree (i + 1) with hgt | hge
    · rw [coeff_eq_zero_of_natDegree_lt hgt, coeff_eq_zero_of_natDegree_lt (by omega),
        mul_zero, sub_zero]
    · have hi : i + 1 = Q.natDegree := by omega
      have hi' : i = Q.natDegree - 1 := by omega
      rw [hi, hQ.coeff_natDegree, mul_one, hi', sub_self]
  have hsplit := modByMonic_add_div (X ^ k) Q
  refine (div_modByMonic_unique (X * (X ^ k /ₘ Q) + C ((X ^ k %ₘ Q).coeff (Q.natDegree - 1)))
    _ hQ ⟨?_, degree_lt_degree (by omega)⟩).2
  linear_combination X * hsplit

/-- `len (Yᵏ %ₘ Q) ≤ (1 + len Q)ᵏ`, and the coefficients of `Yᵏ %ₘ Q` have `X`-degree at
most `k D`. -/
theorem X_pow_modByMonic_le {Q : Polynomial (Polynomial ℤ)} (hQ : Q.Monic)
    (hd : 1 ≤ Q.natDegree) {D : ℕ} (hD : ∀ j, (Q.coeff j).natDegree ≤ D) :
    ∀ k : ℕ, len (X ^ k %ₘ Q) ≤ (1 + len Q) ^ k ∧
      ∀ j, ((X ^ k %ₘ Q).coeff j).natDegree ≤ k * D
  | 0 => by
    have h1 : (X ^ 0 : Polynomial (Polynomial ℤ)) %ₘ Q = 1 := by
      rw [pow_zero, modByMonic_eq_self_iff hQ]
      exact degree_lt_degree (by rw [natDegree_one]; omega)
    rw [h1, pow_zero, Nat.zero_mul]
    refine ⟨le_of_eq len_one, fun j => ?_⟩
    rw [← C_1]
    exact (degX_C 1 j).trans (le_of_eq natDegree_one)
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := X_pow_modByMonic_le hQ hd hD k
    have hkD : (k + 1) * D = k * D + D := by ring
    rw [X_pow_succ_modByMonic hQ hd k]
    refine ⟨?_, ?_⟩
    · calc len (X * (X ^ k %ₘ Q) - C ((X ^ k %ₘ Q).coeff (Q.natDegree - 1)) * Q)
          ≤ len (X * (X ^ k %ₘ Q)) + len (C ((X ^ k %ₘ Q).coeff (Q.natDegree - 1)) * Q) :=
            len_sub_le _ _
        _ ≤ len (X ^ k %ₘ Q) + len (X ^ k %ₘ Q) * len Q := by
            refine Nat.add_le_add ?_ ?_
            · refine (len_mul_le _ _).trans (le_of_eq ?_)
              rw [len_X, Nat.one_mul]
            · refine (len_mul_le _ _).trans (Nat.mul_le_mul_right _ ?_)
              rw [len_C]
              exact len1_coeff_le _ _
        _ = len (X ^ k %ₘ Q) * (1 + len Q) := by ring
        _ ≤ (1 + len Q) ^ k * (1 + len Q) := Nat.mul_le_mul_right _ ih1
        _ = (1 + len Q) ^ (k + 1) := (pow_succ _ _).symm
    · refine degX_sub (fun i => (degX_mul degX_X ih2 i).trans ?_)
        (fun i => (degX_mul (fun i => (degX_C _ i).trans (ih2 _)) hD i).trans (le_of_eq hkD.symm))
      rw [Nat.zero_add, hkD]
      exact Nat.le_add_right _ _

/-! ### Linearity of the remainder -/

theorem modByMonic_eq_sum (Q P : Polynomial (Polynomial ℤ)) :
    P %ₘ Q = ∑ k ∈ Finset.range (P.natDegree + 1), C (P.coeff k) * (X ^ k %ₘ Q) := by
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow]
  rw [← modByMonicHom_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [modByMonicHom_apply, ← smul_eq_C_mul, smul_modByMonic]

theorem main_monic {Q : Polynomial (Polynomial ℤ)} (hQ : Q.Monic) (hd : 1 ≤ Q.natDegree)
    (P : Polynomial (Polynomial ℤ)) (b e n : ℕ) (hb : len P ≤ b)
    (he : ∀ k, (P.coeff k).natDegree ≤ e) (hn : P.natDegree ≤ n) :
    len (P %ₘ Q) ≤ (1 + len Q + degXQ Q) ^ n * b ∧
      ∀ k, ((P %ₘ Q).coeff k).natDegree ≤ e + (1 + len Q + degXQ Q) * n := by
  have hR := X_pow_modByMonic_le hQ hd (natDegree_coeff_le_degXQ Q)
  have hK : 1 ≤ 1 + len Q + degXQ Q := by omega
  rw [modByMonic_eq_sum Q P]
  refine ⟨?_, fun j => ?_⟩
  · calc len (∑ k ∈ Finset.range (P.natDegree + 1), C (P.coeff k) * (X ^ k %ₘ Q))
        ≤ ∑ k ∈ Finset.range (P.natDegree + 1), len (C (P.coeff k) * (X ^ k %ₘ Q)) :=
          len_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (P.natDegree + 1),
            len1 (P.coeff k) * (1 + len Q + degXQ Q) ^ n := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkn : k ≤ n := by
            have := Finset.mem_range.mp hk
            omega
          refine (len_mul_le _ _).trans ?_
          rw [len_C]
          refine Nat.mul_le_mul_left _ ((hR k).1.trans ?_)
          calc (1 + len Q) ^ k ≤ (1 + len Q + degXQ Q) ^ k :=
                Nat.pow_le_pow_left (Nat.le_add_right _ _) k
            _ ≤ (1 + len Q + degXQ Q) ^ n := Nat.pow_le_pow_right hK hkn
      _ = len P * (1 + len Q + degXQ Q) ^ n := by
          rw [← Finset.sum_mul, len_eq_sum P supp_subset_range_natDegree_succ]
      _ ≤ b * (1 + len Q + degXQ Q) ^ n := Nat.mul_le_mul_right _ hb
      _ = (1 + len Q + degXQ Q) ^ n * b := Nat.mul_comm _ _
  · rw [finsetSum_coeff]
    refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    have hkn : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    rw [coeff_C_mul]
    refine natDegree_mul_le.trans (Nat.add_le_add (he k) (((hR k).2 j).trans ?_))
    calc k * degXQ Q ≤ n * (1 + len Q + degXQ Q) := Nat.mul_le_mul hkn (Nat.le_add_left _ _)
      _ = (1 + len Q + degXQ Q) * n := Nat.mul_comm _ _

theorem main (Q : Polynomial (Polynomial ℤ)) :
    ∃ C : ℕ, ∀ (P : Polynomial (Polynomial ℤ)) (b e n : ℕ),
      len P ≤ b → (∀ k, (P.coeff k).natDegree ≤ e) → P.natDegree ≤ n →
      len (P %ₘ Q) ≤ C ^ n * b ∧ ∀ k, ((P %ₘ Q).coeff k).natDegree ≤ e + C * n := by
  by_cases hQ : Q.Monic
  · by_cases hd : Q.natDegree = 0
    · refine ⟨1, fun P b e n _ _ _ => ?_⟩
      rw [eq_one_of_monic_natDegree_zero hQ hd, modByMonic_one, len_zero]
      refine ⟨Nat.zero_le _, fun k => ?_⟩
      rw [coeff_zero, natDegree_zero]
      exact Nat.zero_le _
    · exact ⟨1 + len Q + degXQ Q, fun P b e n hb he hn =>
        main_monic hQ (by omega) P b e n hb he hn⟩
  · refine ⟨1, fun P b e n hb he _ => ?_⟩
    rw [modByMonic_eq_of_not_monic P hQ, Nat.one_pow, Nat.one_mul, Nat.one_mul]
    exact ⟨hb, fun k => (he k).trans (Nat.le_add_right _ _)⟩

end S7W3_exists_modByMonic_length_le

theorem solution (Q : Polynomial (Polynomial ℤ)) :
    ∃ C : ℕ, ∀ (P : Polynomial (Polynomial ℤ)) (b e n : ℕ),
      ∑ k ∈ P.support, ∑ i ∈ (P.coeff k).support, ((P.coeff k).coeff i).natAbs ≤ b →
      (∀ k, (P.coeff k).natDegree ≤ e) → P.natDegree ≤ n →
      ∑ k ∈ (P.modByMonic Q).support, ∑ i ∈ ((P.modByMonic Q).coeff k).support,
          (((P.modByMonic Q).coeff k).coeff i).natAbs ≤ C ^ n * b ∧
        ∀ k, ((P.modByMonic Q).coeff k).natDegree ≤ e + C * n := by
  exact S7W3_exists_modByMonic_length_le.main Q

#print axioms solution
