-- Prove2me | solution 1 for PrivateContinualCounting.Kraft.kraft_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:45:00.469831+00:00
-- url     : https://prove2.me/submissions/96a48c17-468a-44fd-a619-b8074194ce9f

import Definitions.Def_PrivateContinualCounting_Kraft_LTIFactors
import Definitions.Def_PrivateContinualCounting_Kraft_Envelopes

set_option autoImplicit false

open Finset Filter Topology PowerSeries

namespace PCCKraftSuff

noncomputable def bco (r : ℕ → ℝ) (n : ℕ) : ℝ := coeff n (mk r)⁻¹

noncomputable def lco (r : ℕ → ℝ) (s : ℕ) : ℝ := ∑ k ∈ range (s + 1), bco r k

lemma bco_rel (r : ℕ → ℝ) (h0 : r 0 ≠ 0) (n : ℕ) :
    ∑ k ∈ range (n + 1), bco r k * r (n - k) = if n = 0 then 1 else 0 := by
  have h := PowerSeries.inv_mul_cancel (mk r) (by simpa using h0)
  have := congrArg (coeff n) h
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
  rw [coeff_one] at this
  simpa [bco] using this

lemma lco_eq (r : ℕ → ℝ) (s : ℕ) : lco r s = coeff s ((mk r)⁻¹ * mk (fun _ => (1:ℝ))) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [lco, bco]

lemma lco_conv (r : ℕ → ℝ) (h0 : r 0 ≠ 0) (s : ℕ) :
    ∑ j ∈ range (s + 1), lco r j * r (s - j) = 1 := by
  have h := PowerSeries.inv_mul_cancel (mk r) (by simpa using h0)
  have e : ((mk r)⁻¹ * mk (fun _ => (1:ℝ))) * mk r = mk (fun _ => (1:ℝ)) := by
    rw [mul_comm, ← mul_assoc, mul_comm (mk r), h, one_mul]
  have := congrArg (coeff s) e
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
  simpa [← lco_eq] using this

lemma logconvex_cross (r : ℕ → ℝ) (hpos : ∀ k, 0 < r k)
    (h1 : ∀ k, r (k + 1) ^ 2 ≤ r k * r (k + 2)) :
    ∀ a b, a ≤ b → r (a + 1) * r b ≤ r a * r (b + 1) := by
  have hmono : Monotone (fun k => r (k + 1) / r k) := by
    apply monotone_nat_of_le_succ
    intro k
    rw [div_le_div_iff₀ (hpos k) (hpos (k + 1))]
    have := h1 k
    nlinarith
  intro a b hab
  have := hmono hab
  simp only at this
  rw [div_le_div_iff₀ (hpos a) (hpos b)] at this
  linarith

lemma bco_nonpos (r : ℕ → ℝ) (hpos : ∀ k, 0 < r k)
    (hlc : ∀ a b, a ≤ b → r (a + 1) * r b ≤ r a * r (b + 1)) :
    ∀ n, 1 ≤ n → bco r n ≤ 0 := by
  have h0 : r 0 ≠ 0 := (hpos 0).ne'
  have hb0 : bco r 0 * r 0 = 1 := by simpa using bco_rel r h0 0
  have hb0pos : 0 < bco r 0 := by
    by_contra h
    push Not at h
    nlinarith [hpos 0]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have R1 := bco_rel r h0 1
      simp [sum_range_succ] at R1
      -- bco 0 * r 1 + bco 1 * r 0 = 0
      have : bco r 1 * r 0 ≤ 0 := by nlinarith [hpos 1]
      exact nonpos_of_mul_nonpos_left this (hpos 0)
    · have R1 := bco_rel r h0 (m + 1)
      have R0 := bco_rel r h0 m
      rw [if_neg (by omega)] at R1 R0
      rw [sum_range_succ', sum_range_succ] at R1
      rw [sum_range_succ'] at R0
      simp only [Nat.add_sub_add_right, Nat.sub_zero, Nat.sub_self] at R1 R0
      -- R1 : Σ_{k<m} b(k+1) r(m-k) + b(m+1) r 0 + b 0 r(m+1) = 0
      -- R0 : Σ_{k<m} b(k+1) r(m-(k+1)) + b 0 r m = 0
      have hsum : ∑ k ∈ range m,
          bco r (k + 1) * (r (m - (k + 1)) * r (m + 1) - r (m - k) * r m) ≤ 0 := by
        apply sum_nonpos
        intro k hk
        have hk' : k < m := mem_range.mp hk
        have hb : bco r (k + 1) ≤ 0 := ih (k + 1) (by omega) (by omega)
        have hc := hlc (m - (k + 1)) m (by omega)
        have e : m - (k + 1) + 1 = m - k := by omega
        rw [e] at hc
        exact mul_nonpos_of_nonpos_of_nonneg hb (by linarith)
      have e2 : ∑ k ∈ range m, bco r (k + 1) * (r (m - (k + 1)) * r (m + 1) - r (m - k) * r m) =
          r (m + 1) * ∑ k ∈ range m, bco r (k + 1) * r (m - (k + 1)) -
            r m * ∑ k ∈ range m, bco r (k + 1) * r (m - k) := by
        rw [mul_sum, mul_sum, ← sum_sub_distrib]
        apply sum_congr rfl; intro k _; ring
      rw [e2] at hsum
      have : bco r (m + 1) * (r 0 * r m) ≤ 0 := by
        have : bco r (m + 1) * (r 0 * r m) =
            (r (m + 1) * ∑ k ∈ range m, bco r (k + 1) * r (m - (k + 1)) -
              r m * ∑ k ∈ range m, bco r (k + 1) * r (m - k)) := by
          linear_combination (r m) * R1 - (r (m + 1)) * R0
        linarith
      exact nonpos_of_mul_nonpos_left this (mul_pos (hpos 0) (hpos m))

lemma lco_succ (r : ℕ → ℝ) (s : ℕ) : lco r (s + 1) = lco r s + bco r (s + 1) := by
  simp [lco, sum_range_succ _ (s + 1)]

lemma lco_nonneg (r : ℕ → ℝ) (hpos : ∀ k, 0 < r k) (hanti : Antitone r)
    (hlc : ∀ a b, a ≤ b → r (a + 1) * r b ≤ r a * r (b + 1)) (n : ℕ) : 0 ≤ lco r n := by
  have h0 : r 0 ≠ 0 := (hpos 0).ne'
  have hb := bco_nonpos r hpos hlc
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hb0 : bco r 0 * r 0 = 1 := by simpa using bco_rel r h0 0
    simp only [lco, zero_add, sum_range_one]
    by_contra h; push Not at h; nlinarith [hpos 0]
  · have R := bco_rel r h0 n
    rw [if_neg (by omega)] at R
    have : ∑ k ∈ range (n + 1), bco r k * r (n - k) ≤ ∑ k ∈ range (n + 1), bco r k * r n := by
      apply sum_le_sum
      intro k hk
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; simp
      · exact mul_le_mul_of_nonpos_left (hanti (Nat.sub_le n k)) (hb k hk0)
    rw [R, ← sum_mul] at this
    have : 0 ≤ lco r n * r n := by simpa [lco] using this
    exact nonneg_of_mul_nonneg_left this (hpos n)

lemma lco_mul_partial_le (r : ℕ → ℝ) (hpos : ∀ k, 0 < r k) (hanti : Antitone r)
    (hlc : ∀ a b, a ≤ b → r (a + 1) * r b ≤ r a * r (b + 1)) (s : ℕ) :
    lco r s * ∑ k ∈ range (s + 1), r k ≤ 1 := by
  have h0 : r 0 ≠ 0 := (hpos 0).ne'
  have hb := bco_nonpos r hpos hlc
  have hanti_l : ∀ j, j ≤ s → lco r s ≤ lco r j := by
    intro j hj
    induction s, hj using Nat.le_induction with
    | base => exact le_rfl
    | succ s hjs ih =>
      rw [lco_succ]
      have := hb (s + 1) (by omega)
      linarith
  rw [← lco_conv r h0 s, mul_sum]
  calc ∑ k ∈ range (s + 1), lco r s * r k
      = ∑ j ∈ range (s + 1), lco r s * r (s + 1 - 1 - j) := (sum_range_reflect _ _).symm
    _ ≤ ∑ j ∈ range (s + 1), lco r j * r (s - j) := by
        apply sum_le_sum
        intro j hj
        have hj' : j ≤ s := Nat.lt_succ_iff.mp (mem_range.mp hj)
        simp only [Nat.add_sub_cancel]
        exact mul_le_mul_of_nonneg_right (hanti_l j hj') (hpos _).le

end PCCKraftSuff


open Finset Filter Topology

namespace PCCKraftSuff

/-- Geometric mixture parameters. -/
noncomputable def rho (n : ℕ) : ℝ := 1 - (1 / 4 : ℝ) ^ n

noncomputable def wt (a : ℕ → ℝ) (n : ℕ) : ℝ := a n * (1 / 2 : ℝ) ^ n

noncomputable def mix (a : ℕ → ℝ) (k : ℕ) : ℝ := ∑' n, wt a n * rho n ^ k

lemma rho_nonneg (n : ℕ) : 0 ≤ rho n := by
  unfold rho
  have : (1 / 4 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

lemma rho_le_one (n : ℕ) : rho n ≤ 1 := by
  unfold rho
  have : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
  linarith

section
variable (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)

include ha0 in
lemma wt_nonneg (n : ℕ) : 0 ≤ wt a n := by unfold wt; have := ha0 n; positivity

include ha0 in
lemma term_nonneg (n k : ℕ) : 0 ≤ wt a n * rho n ^ k :=
  mul_nonneg (wt_nonneg a ha0 n) (pow_nonneg (rho_nonneg n) k)

include ha0 ha1 in
lemma term_summable (k : ℕ) : Summable (fun n => wt a n * rho n ^ k) := by
  refine Summable.of_nonneg_of_le (term_nonneg a ha0 · k) (fun n => ?_)
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num))
  unfold wt
  have h1 := ha1 n
  have h2 : rho n ^ k ≤ 1 := pow_le_one₀ (rho_nonneg n) (rho_le_one n)
  have h3 : 0 ≤ rho n ^ k := pow_nonneg (rho_nonneg n) k
  have h4 : (0:ℝ) ≤ (1 / 2) ^ n := by positivity
  have h5 := ha0 n
  calc a n * (1 / 2) ^ n * rho n ^ k ≤ 1 * (1 / 2) ^ n * 1 := by gcongr
    _ = (1 / 2) ^ n := by ring

include ha0 ha1 in
lemma mix_nonneg (k : ℕ) : 0 ≤ mix a k := tsum_nonneg (term_nonneg a ha0 · k)

include ha0 ha1 in
lemma term_le_mix (n k : ℕ) : wt a n * rho n ^ k ≤ mix a k :=
  (term_summable a ha0 ha1 k).le_tsum n (fun j _ => term_nonneg a ha0 j k)

include ha0 ha1 in
lemma mix_pos (ha : 0 < a 1) (k : ℕ) : 0 < mix a k := by
  refine lt_of_lt_of_le ?_ (term_le_mix a ha0 ha1 1 k)
  unfold wt rho
  norm_num
  positivity

include ha0 ha1 in
lemma mix_anti : Antitone (mix a) := by
  apply antitone_nat_of_succ_le
  intro k
  apply (term_summable a ha0 ha1 (k + 1)).tsum_le_tsum _ (term_summable a ha0 ha1 k)
  intro n
  rw [pow_succ]
  have h := wt_nonneg a ha0 n
  have h1 := rho_le_one n
  have h0 := rho_nonneg n
  have h3 : 0 ≤ rho n ^ k := pow_nonneg h0 k
  calc wt a n * (rho n ^ k * rho n) ≤ wt a n * (rho n ^ k * 1) := by gcongr
    _ = wt a n * rho n ^ k := by ring

include ha0 ha1 in
lemma mix_logconvex (k : ℕ) : mix a (k + 1) ^ 2 ≤ mix a k * mix a (k + 2) := by
  have t := fun j => (term_summable a ha0 ha1 j).hasSum.tendsto_sum_nat
  have hl : Tendsto (fun N => (∑ n ∈ range N, wt a n * rho n ^ (k + 1)) ^ 2) atTop
      (𝓝 (mix a (k + 1) ^ 2)) := (t (k + 1)).pow 2
  have hr : Tendsto (fun N => (∑ n ∈ range N, wt a n * rho n ^ k) *
      ∑ n ∈ range N, wt a n * rho n ^ (k + 2)) atTop (𝓝 (mix a k * mix a (k + 2))) :=
    (t k).mul (t (k + 2))
  refine le_of_tendsto_of_tendsto' hl hr (fun N => ?_)
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro n _; exact term_nonneg a ha0 n k
  · intro n _; exact term_nonneg a ha0 n (k + 2)
  · intro n _; apply le_of_eq; ring

include ha0 ha1 in
/-- Lower bound for the partial sums of the strategy. -/
lemma partial_lower (n s : ℕ) (hn : 1 ≤ n) (hs : 4 ^ (n - 1) ≤ s + 1) :
    3 / 16 * a n * 2 ^ n ≤ ∑ k ∈ range (s + 1), mix a k := by
  set N := 4 ^ (n - 1) with hN
  have hρN : 3 / 4 ≤ rho n ^ N := by
    have hb := one_add_mul_le_pow (a := -(1 / 4 : ℝ) ^ n)
      (by have : (1 / 4 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num); linarith) N
    have e : (N : ℝ) * (1 / 4 : ℝ) ^ n = 1 / 4 := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [hN, Nat.add_sub_cancel]
      push_cast
      rw [pow_succ, ← mul_assoc, ← mul_pow]
      norm_num
    unfold rho
    have : 1 + (N:ℝ) * -(1 / 4 : ℝ) ^ n = 3 / 4 := by rw [mul_neg, e]; norm_num
    rw [sub_eq_add_neg]
    linarith
  have hwn := wt_nonneg a ha0 n
  have halg : 3 / 16 * a n * 2 ^ n = (N : ℝ) * wt a n * (3 / 4) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [hN, Nat.add_sub_cancel, wt]
    push_cast
    have e4 : (4:ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
    rw [e4, one_div_pow]
    field_simp
    ring
  rw [halg]
  calc (N : ℝ) * wt a n * (3 / 4) ≤ (N : ℝ) * wt a n * rho n ^ N := by gcongr
    _ = ∑ k ∈ range N, wt a n * rho n ^ N := by rw [sum_const, card_range, nsmul_eq_mul, mul_assoc]
    _ ≤ ∑ k ∈ range N, wt a n * rho n ^ k := by
        apply sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (rho_nonneg n) (rho_le_one n) (mem_range.mp hk).le) hwn
    _ ≤ ∑ k ∈ range N, mix a k := sum_le_sum (fun k _ => term_le_mix a ha0 ha1 n k)
    _ ≤ ∑ k ∈ range (s + 1), mix a k :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hs)
          (fun k _ _ => mix_nonneg a ha0 ha1 k)


/-- Cross kernel bounding the Gram matrix of the geometric components. -/
noncomputable def Kc (n m : ℕ) : ℝ := (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ m * 4 ^ (min n m)

lemma Kc_nonneg (n m : ℕ) : 0 ≤ Kc n m := by unfold Kc; positivity

lemma Kc_symm (n m : ℕ) : Kc n m = Kc m n := by unfold Kc; rw [min_comm]; ring

lemma one_sub_rho_mul (n m : ℕ) : (1 / 4 : ℝ) ^ (min n m) ≤ 1 - rho n * rho m := by
  rcases le_total n m with h | h
  · rw [min_eq_left h]
    have : rho n * rho m ≤ rho n := mul_le_of_le_one_right (rho_nonneg n) (rho_le_one m)
    unfold rho at this ⊢; linarith
  · rw [min_eq_right h]
    have : rho n * rho m ≤ rho m := mul_le_of_le_one_left (rho_nonneg m) (rho_le_one n)
    unfold rho at this ⊢; linarith

lemma geom_two_sum (n : ℕ) : ∑ m ∈ range n, (2:ℝ) ^ m + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; linarith

lemma Kc_lower_sum (n : ℕ) : ∑ m ∈ range n, Kc n m ≤ 1 := by
  have : ∑ m ∈ range n, Kc n m = (1 / 2 : ℝ) ^ n * ∑ m ∈ range n, (2:ℝ) ^ m := by
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    have hmn : m ≤ n := (mem_range.mp hm).le
    unfold Kc
    rw [min_eq_right hmn, mul_assoc, ← mul_pow]
    norm_num
  rw [this]
  have h2 := geom_two_sum n
  have h3 : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
  have h4 : (0:ℝ) ≤ (1 / 2) ^ n := by positivity
  nlinarith

lemma Kc_tail (n i : ℕ) : Kc n (i + n) = (1 / 2 : ℝ) ^ i := by
  unfold Kc
  rw [min_eq_left (by omega), pow_add]
  have e4 : (4:ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  have e5 : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [e4]
  calc (1 / 2 : ℝ) ^ n * ((1 / 2) ^ i * (1 / 2) ^ n) * (2 ^ n * 2 ^ n)
      = (1 / 2) ^ i * ((1 / 2 : ℝ) ^ n * 2 ^ n) * ((1 / 2 : ℝ) ^ n * 2 ^ n) := by ring
    _ = (1 / 2) ^ i := by rw [e5]; ring

lemma Kc_tail_sum (n : ℕ) : ∑' i, ENNReal.ofReal (Kc n (i + n)) = 2 := by
  have e : ∀ i, ENNReal.ofReal (Kc n (i + n)) = (2⁻¹ : ENNReal) ^ i := by
    intro i
    rw [Kc_tail, ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  simp_rw [e]
  rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]

lemma Kc_row (n : ℕ) : ∑' m, ENNReal.ofReal (Kc n m) ≤ 3 := by
  have hsplit := Summable.sum_add_tsum_nat_add' (f := fun m => ENNReal.ofReal (Kc n m)) (k := n)
    ENNReal.summable
  rw [← hsplit, Kc_tail_sum]
  have h1 : ∑ m ∈ range n, ENNReal.ofReal (Kc n m) ≤ 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => Kc_nonneg n m)]
    exact ENNReal.ofReal_le_one.mpr (Kc_lower_sum n)
  calc ∑ m ∈ range n, ENNReal.ofReal (Kc n m) + 2 ≤ 1 + 2 := by gcongr
    _ = 3 := by norm_num

include ha0 ha1 in
lemma pair_bound (n m : ℕ) :
    ∑' k, ENNReal.ofReal (wt a n * rho n ^ k) * ENNReal.ofReal (wt a m * rho m ^ k) ≤
      ENNReal.ofReal (a n ^ 2 * Kc n m) + ENNReal.ofReal (a m ^ 2 * Kc n m) := by
  have hA := wt_nonneg a ha0 n
  have hB := wt_nonneg a ha0 m
  have hρ := mul_nonneg (rho_nonneg n) (rho_nonneg m)
  have hpos : 0 < 1 - rho n * rho m :=
    lt_of_lt_of_le (by positivity) (one_sub_rho_mul n m)
  have e : ∀ k, ENNReal.ofReal (wt a n * rho n ^ k) * ENNReal.ofReal (wt a m * rho m ^ k) =
      ENNReal.ofReal (wt a n * wt a m) * ENNReal.ofReal (rho n * rho m) ^ k := by
    intro k
    rw [← ENNReal.ofReal_mul (term_nonneg a ha0 n k), ← ENNReal.ofReal_pow hρ,
      ← ENNReal.ofReal_mul (mul_nonneg hA hB), mul_pow]
    congr 1; ring
  simp_rw [e]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 hρ, ← ENNReal.ofReal_inv_of_pos hpos,
    ← ENNReal.ofReal_mul (mul_nonneg hA hB),
    ← ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (Kc_nonneg n m))
      (mul_nonneg (sq_nonneg _) (Kc_nonneg n m))]
  apply ENNReal.ofReal_le_ofReal
  have hinv : (1 - rho n * rho m)⁻¹ ≤ 4 ^ (min n m) := by
    have := one_sub_rho_mul n m
    calc (1 - rho n * rho m)⁻¹ ≤ ((1 / 4 : ℝ) ^ (min n m))⁻¹ :=
          inv_anti₀ (by positivity) this
      _ = 4 ^ (min n m) := by rw [one_div_pow, one_div, inv_inv]
  have hab : a n * a m ≤ a n ^ 2 + a m ^ 2 := by
    nlinarith [sq_nonneg (a n - a m), ha0 n, ha0 m]
  have hP : (0:ℝ) ≤ (1 / 2) ^ n * (1 / 2) ^ m := by positivity
  have hab0 : 0 ≤ a n * a m := mul_nonneg (ha0 n) (ha0 m)
  calc wt a n * wt a m * (1 - rho n * rho m)⁻¹
      = (a n * a m) * ((1 / 2) ^ n * (1 / 2) ^ m) * (1 - rho n * rho m)⁻¹ := by
        unfold wt; ring
    _ ≤ (a n * a m) * ((1 / 2) ^ n * (1 / 2) ^ m) * 4 ^ (min n m) := by gcongr
    _ ≤ (a n ^ 2 + a m ^ 2) * ((1 / 2) ^ n * (1 / 2) ^ m) * 4 ^ (min n m) := by gcongr
    _ = a n ^ 2 * Kc n m + a m ^ 2 * Kc n m := by unfold Kc; ring

include ha0 ha1 in
lemma mix_sq_summable (ha2 : Summable (fun n => a n ^ 2)) : Summable (fun k => mix a k ^ 2) := by
  set x : ℕ → ℕ → ENNReal := fun n k => ENNReal.ofReal (wt a n * rho n ^ k) with hxdef
  have hx : ∀ k, ENNReal.ofReal (mix a k) = ∑' n, x n k := fun k =>
    ENNReal.ofReal_tsum_of_nonneg (term_nonneg a ha0 · k) (term_summable a ha0 ha1 k)
  have hsq : ∀ k, ENNReal.ofReal (mix a k ^ 2) = ∑' n, ∑' m, x n k * x m k := by
    intro k
    rw [ENNReal.ofReal_pow (mix_nonneg a ha0 ha1 k), hx, sq, ← ENNReal.tsum_mul_right]
    congr 1; ext n
    rw [← ENNReal.tsum_mul_left]
  have hA : ∑' n, ENNReal.ofReal (a n ^ 2) = ENNReal.ofReal (∑' n, a n ^ 2) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) ha2).symm
  have hbound : ∑' k, ENNReal.ofReal (mix a k ^ 2) ≤ 6 * ENNReal.ofReal (∑' n, a n ^ 2) := by
    simp_rw [hsq]
    rw [ENNReal.tsum_comm]
    have : ∀ n, ∑' k, ∑' m, x n k * x m k = ∑' m, ∑' k, x n k * x m k :=
      fun n => ENNReal.tsum_comm
    simp_rw [this]
    calc ∑' n, ∑' m, ∑' k, x n k * x m k
        ≤ ∑' n, ∑' m, (ENNReal.ofReal (a n ^ 2 * Kc n m) + ENNReal.ofReal (a m ^ 2 * Kc n m)) :=
          ENNReal.tsum_le_tsum (fun n => ENNReal.tsum_le_tsum (fun m => pair_bound a ha0 ha1 n m))
      _ = ∑' n, ∑' m, ENNReal.ofReal (a n ^ 2 * Kc n m) +
            ∑' n, ∑' m, ENNReal.ofReal (a m ^ 2 * Kc n m) := by
          simp_rw [ENNReal.tsum_add]
      _ = 2 * ∑' n, ∑' m, ENNReal.ofReal (a n ^ 2 * Kc n m) := by
          rw [two_mul]
          congr 1
          rw [ENNReal.tsum_comm]
          congr 1; ext n; congr 1; ext m
          rw [Kc_symm]
      _ ≤ 2 * ∑' n, ENNReal.ofReal (a n ^ 2) * 3 := by
          gcongr with n
          simp_rw [ENNReal.ofReal_mul (sq_nonneg (a n))]
          rw [ENNReal.tsum_mul_left]
          gcongr
          exact Kc_row n
      _ = 6 * ENNReal.ofReal (∑' n, a n ^ 2) := by
          rw [ENNReal.tsum_mul_right, hA, ← mul_assoc, mul_comm _ (3 : ENNReal), ← mul_assoc]
          norm_num
  have hfin : ∑' k, ENNReal.ofReal (mix a k ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hbound
  exact (ENNReal.summable_toReal hfin).congr (fun k => ENNReal.toReal_ofReal (sq_nonneg _))

end

end PCCKraftSuff


open Finset Filter Topology

namespace PCCKraftSuff
open PrivateContinualCounting.Kraft

/-- Envelope-adapted weights: `a n ^ 2 = 1/(n g(n))`. -/
noncomputable def aw (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else Real.sqrt (1 / ((n:ℝ) * g n))

section
variable (g : ℝ → ℝ) (D : ℝ) (hg : IsEnvelopeWith g D)

include hg in
lemma g_pos (u : ℝ) (hu : 1 ≤ u) : 0 < g u := lt_of_lt_of_le one_pos (hg.2.1 u hu)

lemma aw_nonneg (n : ℕ) : 0 ≤ aw g n := by
  unfold aw; split_ifs <;> positivity

include hg in
lemma aw_sq (n : ℕ) (hn : 1 ≤ n) : aw g n ^ 2 = 1 / ((n:ℝ) * g n) := by
  unfold aw
  rw [if_neg (by omega)]
  have : (1:ℝ) ≤ n := by exact_mod_cast hn
  have := g_pos g D hg n this
  rw [Real.sq_sqrt (by positivity)]

include hg in
lemma aw_le_one (n : ℕ) : aw g n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [aw]
  · have hn : (1:ℝ) ≤ n := by exact_mod_cast h
    have hgn := hg.2.1 n hn
    have h2 := aw_sq g D hg n h
    have : 1 / ((n:ℝ) * g n) ≤ 1 := by
      rw [div_le_one (by nlinarith)]; nlinarith
    have h0 := aw_nonneg g n
    nlinarith

include hg in
lemma aw_one_pos : 0 < aw g 1 := by
  unfold aw
  rw [if_neg (by norm_num)]
  have := g_pos g D hg 1 le_rfl
  apply Real.sqrt_pos.2
  push_cast
  positivity

include hg in
lemma aw_sq_summable (hK : KraftCondition g) : Summable (fun n => aw g n ^ 2) := by
  have hmono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → aw g n ^ 2 ≤ aw g m ^ 2 := by
    intro m n hm hmn
    rw [aw_sq g D hg n (by omega), aw_sq g D hg m hm]
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
    have hmn' : (m:ℝ) ≤ n := by exact_mod_cast hmn
    have hgm := hg.2.1 m hm1
    have hgmn : g m ≤ g n := hg.2.2.1 (Set.mem_Ici.mpr hm1) (Set.mem_Ici.mpr (hm1.trans hmn')) hmn'
    apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul hmn' hgmn (by linarith) (by linarith)
  rw [← summable_condensed_iff_of_nonneg (fun n => sq_nonneg _) hmono]
  refine hK.congr (fun k => ?_)
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [aw_sq g D hg _ hk]
  push_cast
  have h2 : (0:ℝ) < 2 ^ k := by positivity
  have := g_pos g D hg (2 ^ k) (one_le_pow₀ (by norm_num))
  field_simp


include hg in
lemma r_props :
    (∀ k, 0 < mix (aw g) k) ∧ Antitone (mix (aw g)) ∧
    (∀ a b, a ≤ b → mix (aw g) (a + 1) * mix (aw g) b ≤ mix (aw g) a * mix (aw g) (b + 1)) := by
  have ha0 := aw_nonneg g
  have ha1 := aw_le_one g D hg
  have hpos := mix_pos (aw g) ha0 ha1 (aw_one_pos g D hg)
  refine ⟨hpos, mix_anti (aw g) ha0 ha1, ?_⟩
  exact logconvex_cross _ hpos (mix_logconvex (aw g) ha0 ha1)

include hg in
lemma l_sq_bound (s : ℕ) (hs : 1 ≤ s) :
    lco (mix (aw g)) s ^ 2 * s ≤
      29 * (((Nat.log 4 s + 1 : ℕ) : ℝ) * g ((Nat.log 4 s + 1 : ℕ) : ℝ)) := by
  obtain ⟨hpos, hanti, hlc⟩ := r_props g D hg
  have ha0 := aw_nonneg g
  have ha1 := aw_le_one g D hg
  set n := Nat.log 4 s + 1 with hn
  have hn1 : 1 ≤ n := by omega
  have h4 : 4 ^ (n - 1) ≤ s + 1 := by
    have := Nat.pow_log_le_self 4 (show s ≠ 0 by omega)
    simp only [hn, Nat.add_sub_cancel]; omega
  have hsn : s < 4 ^ n := Nat.lt_pow_succ_log_self (by norm_num) s
  have hX := partial_lower (aw g) ha0 ha1 n s hn1 h4
  have hl := lco_mul_partial_le _ hpos hanti hlc s
  have hl0 := lco_nonneg _ hpos hanti hlc s
  set l := lco (mix (aw g)) s
  set X := 3 / 16 * aw g n * 2 ^ n with hXdef
  have hX0 : 0 ≤ X := by have := ha0 n; positivity
  have hlX : l * X ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hX hl0) hl
  have hlX2 : (l * X) ^ 2 ≤ 1 := by
    have : 0 ≤ l * X := mul_nonneg hl0 hX0
    nlinarith
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hgn := g_pos g D hg n hn'
  have hsq := aw_sq g D hg n hn1
  have hX2 : X ^ 2 = 9 / 256 * (4:ℝ) ^ n / ((n:ℝ) * g n) := by
    rw [hXdef, mul_pow, mul_pow, hsq]
    have e : ((2:ℝ) ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e]; field_simp; ring
  have h1 : l ^ 2 * (9 / 256 * (4:ℝ) ^ n) ≤ (n:ℝ) * g n := by
    have : l ^ 2 * X ^ 2 ≤ 1 := by rw [← mul_pow]; exact hlX2
    rw [hX2] at this
    have hng : (0:ℝ) < (n:ℝ) * g n := by positivity
    have e : l ^ 2 * (9 / 256 * 4 ^ n / (↑n * g ↑n)) = (l ^ 2 * (9 / 256 * (4:ℝ) ^ n)) / (↑n * g ↑n) := by
      ring
    rw [e, div_le_one hng] at this
    exact this
  have hs4 : (s:ℝ) ≤ 4 ^ n := by exact_mod_cast hsn.le
  have hl2 : 0 ≤ l ^ 2 := sq_nonneg l
  have h2 : l ^ 2 * (9 / 256 * (s:ℝ)) ≤ (n:ℝ) * g n :=
    le_trans (by gcongr) h1
  have hng0 : (0:ℝ) ≤ (n:ℝ) * g n := by positivity
  nlinarith


lemma one_le_log_nat (t : ℕ) (ht : 3 ≤ t) : 1 ≤ Real.log (t:ℝ) := by
  have h3 : (3:ℝ) ≤ t := by exact_mod_cast ht
  have : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  linarith [Real.log_le_log (by norm_num) h3]

include hg in
lemma energy_bound (t : ℕ) (ht : 3 ≤ t) :
    ∑ j ∈ range t, lco (mix (aw g)) j ^ 2 ≤
      (lco (mix (aw g)) 0 ^ 2 + 116 * D) * (Real.log (t:ℝ)) ^ 2 * g (Real.log (t:ℝ)) := by
  set l := lco (mix (aw g)) with hldef
  set L := Real.log (t:ℝ) with hLdef
  have hL1 : 1 ≤ L := one_le_log_nat t ht
  have hD1 : 1 ≤ D := hg.1
  have hgL : 1 ≤ g L := hg.2.1 L hL1
  set N := Nat.log 4 t + 1 with hN
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hgN := g_pos g D hg N hN1
  -- each term
  have hterm : ∀ s ∈ Ico 1 t, l s ^ 2 ≤ 29 * ((N:ℝ) * g N) * (1 / (s:ℝ)) := by
    intro s hs
    have hs1 : 1 ≤ s := (mem_Ico.mp hs).1
    have hst : s ≤ t := (mem_Ico.mp hs).2.le
    have hb := l_sq_bound g D hg s hs1
    have hns : Nat.log 4 s + 1 ≤ N := by
      have := Nat.log_mono_right (b := 4) hst; omega
    have hns' : (((Nat.log 4 s + 1 : ℕ)) : ℝ) ≤ N := by exact_mod_cast hns
    have hn1 : (1:ℝ) ≤ ((Nat.log 4 s + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ Nat.log 4 s + 1 by omega)
    have hgmono : g ((Nat.log 4 s + 1 : ℕ) : ℝ) ≤ g N :=
      hg.2.2.1 (Set.mem_Ici.mpr hn1) (Set.mem_Ici.mpr hN1) hns'
    have hg1 := g_pos g D hg _ hn1
    have hsp : (0:ℝ) < s := by exact_mod_cast hs1
    rw [mul_one_div, le_div_iff₀ hsp]
    calc l s ^ 2 * s ≤ 29 * (((Nat.log 4 s + 1 : ℕ) : ℝ) * g ((Nat.log 4 s + 1 : ℕ) : ℝ)) := hb
      _ ≤ 29 * ((N:ℝ) * g N) := by gcongr
  have hharm : ∑ s ∈ Ico 1 t, 1 / (s:ℝ) ≤ 1 + L := by
    rw [sum_Ico_eq_sum_range]
    have h1 : ∑ k ∈ range (t - 1), 1 / ((1 + k : ℕ) : ℝ) ≤ ∑ k ∈ range t, 1 / ((k:ℝ) + 1) := by
      calc ∑ k ∈ range (t - 1), 1 / ((1 + k : ℕ) : ℝ) = ∑ k ∈ range (t - 1), 1 / ((k:ℝ) + 1) := by
            apply sum_congr rfl; intro k _; push_cast; ring
        _ ≤ ∑ k ∈ range t, 1 / ((k:ℝ) + 1) :=
            sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
              (fun k _ _ => by positivity)
    have h2 : ∑ k ∈ range t, 1 / ((k:ℝ) + 1) ≤ 1 + L := by
      have := harmonic_le_one_add_log t
      simpa [harmonic] using this
    linarith
  have hNL : (N:ℝ) ≤ 2 * L := by
    have hp : 4 ^ (Nat.log 4 t) ≤ t := Nat.pow_log_le_self 4 (by omega)
    have hp' : (4:ℝ) ^ (Nat.log 4 t) ≤ t := by exact_mod_cast hp
    have hlog := Real.log_le_log (by positivity) hp'
    rw [Real.log_pow] at hlog
    have hl4 : 1 ≤ Real.log 4 := by
      have : (4:ℝ) = 2 ^ 2 := by norm_num
      rw [this, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast; linarith
    have hk0 : (0:ℝ) ≤ (Nat.log 4 t : ℝ) := Nat.cast_nonneg _
    have : (Nat.log 4 t : ℝ) ≤ L := by nlinarith
    have e : (N:ℝ) = (Nat.log 4 t : ℝ) + 1 := by rw [hN]; push_cast; ring
    linarith
  have hgNL : g N ≤ D * g L := by
    have h1 : g N ≤ g (2 * L) :=
      hg.2.2.1 (Set.mem_Ici.mpr hN1) (Set.mem_Ici.mpr (by linarith)) hNL
    exact h1.trans (hg.2.2.2 L hL1)
  have hsplit := sum_range_add_sum_Ico (fun j => l j ^ 2) (show 1 ≤ t by omega)
  rw [← hsplit]
  have hIco : ∑ s ∈ Ico 1 t, l s ^ 2 ≤ 116 * D * (L ^ 2 * g L) := by
    calc ∑ s ∈ Ico 1 t, l s ^ 2 ≤ ∑ s ∈ Ico 1 t, 29 * ((N:ℝ) * g N) * (1 / (s:ℝ)) :=
          sum_le_sum hterm
      _ = 29 * ((N:ℝ) * g N) * ∑ s ∈ Ico 1 t, 1 / (s:ℝ) := by rw [mul_sum]
      _ ≤ 29 * ((2 * L) * (D * g L)) * (2 * L) := by
          have h0 : (0:ℝ) ≤ N := by positivity
          gcongr
          linarith
      _ = 116 * D * (L ^ 2 * g L) := by ring
  have hLg : 1 ≤ L ^ 2 * g L := by nlinarith
  have hl0 : ∑ j ∈ range 1, l j ^ 2 ≤ l 0 ^ 2 * (L ^ 2 * g L) := by
    simp only [sum_range_one]
    have := sq_nonneg (l 0)
    nlinarith
  calc ∑ j ∈ range 1, l j ^ 2 + ∑ s ∈ Ico 1 t, l s ^ 2
      ≤ l 0 ^ 2 * (L ^ 2 * g L) + 116 * D * (L ^ 2 * g L) := add_le_add hl0 hIco
    _ = (l 0 ^ 2 + 116 * D) * L ^ 2 * g L := by ring

end

/-- Sufficiency in Theorem 1.1(ii): a real scalar LTI counter realises every Kraft envelope. -/
theorem kraft_sufficiency (g : ℝ → ℝ) (hg : IsEnvelope g) (hK : KraftCondition g) :
    ∃ M : LTICounter 1, HasEnvelope M.val.variance g := by
  obtain ⟨D, hgD⟩ := hg
  obtain ⟨hpos, hanti, hlc⟩ := r_props g D hgD
  set r := mix (aw g) with hr
  have ha0 := aw_nonneg g
  have ha1 := aw_le_one g D hgD
  have hsum2 : Summable (fun k => r k ^ 2) :=
    mix_sq_summable (aw g) ha0 ha1 (aw_sq_summable g D hgD hK)
  let d : LTIData ℝ 1 := ⟨fun j _ => lco r j, fun k _ => r k⟩
  have hvs : ∀ x : ℝ, vectorSq (fun _ : Fin 1 => x) = x ^ 2 := by
    intro x; simp [vectorSq]
  have hLTI : IsLTI d := by
    refine ⟨one_pos, fun s => ?_, ?_⟩
    · simpa [d] using lco_conv r (hpos 0).ne' s
    · simpa [d, hvs] using hsum2
  refine ⟨⟨d, hLTI⟩, ?_⟩
  have hΔ : d.deltaSq = ∑' k, r k ^ 2 := by simp [LTIData.deltaSq, d, hvs]
  have hE : ∀ t, d.energy t = ∑ j ∈ range t, lco r j ^ 2 := by
    intro t; simp [LTIData.energy, d, hvs]
  have hΔpos : 0 < ∑' k, r k ^ 2 :=
    lt_of_lt_of_le (by have := hpos 0; positivity) (hsum2.le_tsum 0 (fun j _ => sq_nonneg _))
  refine ⟨(∑' k, r k ^ 2) * (lco r 0 ^ 2 + 116 * D), ?_, fun t ht => ?_⟩
  · have := hgD.1; positivity
  · show d.variance t ≤ _
    rw [LTIData.variance, hΔ, hE]
    have := energy_bound g D hgD t ht
    calc (∑' k, r k ^ 2) * ∑ j ∈ range t, lco r j ^ 2
        ≤ (∑' k, r k ^ 2) * ((lco r 0 ^ 2 + 116 * D) * (Real.log (t:ℝ)) ^ 2 * g (Real.log (t:ℝ))) :=
          mul_le_mul_of_nonneg_left this hΔpos.le
      _ = _ := by ring

end PCCKraftSuff


open PrivateContinualCounting.Kraft in
theorem solution (g : ℝ → ℝ) (hg : IsEnvelope g) (hK : KraftCondition g) :
    ∃ M : LTICounter 1, HasEnvelope M.val.variance g :=
  PCCKraftSuff.kraft_sufficiency g hg hK
