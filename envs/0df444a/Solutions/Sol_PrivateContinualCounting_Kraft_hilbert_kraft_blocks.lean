-- Prove2me | solution 1 for PrivateContinualCounting.Kraft.hilbert_kraft_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:44:58.947473+00:00
-- url     : https://prove2.me/submissions/23df5f85-5565-4ace-bd61-91c2d9e888e5

import Theorems.Thm_PrivateContinualCounting_Kraft_hilbert_inequality

set_option autoImplicit false

open Finset Filter Topology

namespace PCCKraftCore

/-- The Hilbert transform `χ_j = Σ_k β_k/(j+k+1)`. -/
noncomputable def chi (β : ℕ → ℝ) (j : ℕ) : ℝ := ∑' k, β k / ((j:ℝ) + k + 1)

lemma chi_summable (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hβ2 : Summable (fun k => β k ^ 2))
    (j : ℕ) : Summable (fun k => β k / ((j:ℝ) + k + 1)) :=
  (PrivateContinualCounting.Kraft.hilbert_inequality β hβ hβ2).1 j

lemma chi_nonneg (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (j : ℕ) : 0 ≤ chi β j :=
  tsum_nonneg (fun k => by have := hβ k; positivity)

lemma sum_le_chi (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hβ2 : Summable (fun k => β k ^ 2))
    (j N : ℕ) : ∑ k ∈ range N, β k / ((j:ℝ) + k + 1) ≤ chi β j :=
  (chi_summable β hβ hβ2 j).sum_le_tsum _ (fun k _ => by have := hβ k; positivity)

lemma chi_sq_summable (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hβ2 : Summable (fun k => β k ^ 2)) :
    Summable (fun j => chi β j ^ 2) :=
  (PrivateContinualCounting.Kraft.hilbert_inequality β hβ hβ2).2.1

lemma chi_sq_sum_le (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hβ2 : Summable (fun k => β k ^ 2))
    (n : ℕ) : ∑ j ∈ range n, chi β j ^ 2 ≤ 16 * ∑' k, β k ^ 2 :=
  ((chi_sq_summable β hβ hβ2).sum_le_tsum _ (fun j _ => sq_nonneg _)).trans
    (PrivateContinualCounting.Kraft.hilbert_inequality β hβ hβ2).2.2

/-- Weighting the convolution identities by `1/(m+1)`. -/
lemma log_le_sum_chi (α β : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j) (hβ : ∀ k, 0 ≤ β k)
    (hβ2 : Summable (fun k => β k ^ 2))
    (hid : ∀ m, 1 ≤ ∑ j ∈ range (m + 1), α j * β (m - j)) (n : ℕ) :
    Real.log ((n:ℝ) + 1) ≤ ∑ j ∈ range n, α j * chi β j := by
  have h1 : Real.log ((n:ℝ) + 1) ≤ ∑ m ∈ range n, 1 / ((m:ℝ) + 1) := by
    have := log_add_one_le_harmonic n
    simpa [harmonic] using this
  refine h1.trans ?_
  set f : ℕ → ℕ → ℝ := fun j k => α j * β k / (((j + k : ℕ) : ℝ) + 1) with hf
  have h2 : ∀ m : ℕ, 1 / ((m:ℝ) + 1) ≤ ∑ j ∈ range (m + 1), f j (m - j) := by
    intro m
    have hm : (0:ℝ) < (m:ℝ) + 1 := by positivity
    have : ∑ j ∈ range (m + 1), f j (m - j) =
        (∑ j ∈ range (m + 1), α j * β (m - j)) / ((m:ℝ) + 1) := by
      rw [sum_div]
      apply sum_congr rfl
      intro j hj
      have hj' : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
      simp only [hf, Nat.add_sub_cancel' hj']
    rw [this]
    exact div_le_div_of_nonneg_right (hid m) hm.le
  calc ∑ m ∈ range n, 1 / ((m:ℝ) + 1) ≤ ∑ m ∈ range n, ∑ j ∈ range (m + 1), f j (m - j) :=
        sum_le_sum (fun m _ => h2 m)
    _ = ∑ j ∈ range n, ∑ k ∈ range (n - j), f j k := sum_range_diag_flip n f
    _ ≤ ∑ j ∈ range n, α j * chi β j := by
        apply sum_le_sum
        intro j _
        have : ∑ k ∈ range (n - j), f j k = α j * ∑ k ∈ range (n - j), β k / ((j:ℝ) + k + 1) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro k _
          simp only [hf]
          push_cast
          ring
        rw [this]
        exact mul_le_mul_of_nonneg_left (sum_le_chi β hβ hβ2 j _) (hα j)


lemma sum_Ico_chi_sq_le (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hβ2 : Summable (fun k => β k ^ 2))
    (J n : ℕ) : ∑ j ∈ Ico J n, chi β j ^ 2 ≤ ∑' i, chi β (i + J) ^ 2 := by
  rw [sum_Ico_eq_sum_range]
  have hs : Summable (fun i => chi β (i + J) ^ 2) :=
    (summable_nat_add_iff J).mpr (chi_sq_summable β hβ hβ2)
  calc ∑ k ∈ range (n - J), chi β (J + k) ^ 2 = ∑ k ∈ range (n - J), chi β (k + J) ^ 2 := by
        simp_rw [add_comm J]
    _ ≤ _ := hs.sum_le_tsum _ (fun i _ => sq_nonneg _)


/-- Block boundaries `0, 2^(2^1), 2^(2^2), …`. -/
def blk (i : ℕ) : ℕ := if i = 0 then 0 else 2 ^ (2 ^ i)

lemma blk_mono : Monotone blk := by
  apply monotone_nat_of_le_succ
  intro i
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp [blk]
  · simp only [blk, if_neg (Nat.pos_iff_ne_zero.mp h), Nat.succ_ne_zero, if_false]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ i))

lemma sum_blocks (f : ℕ → ℝ) (k : ℕ) :
    ∑ j ∈ range (blk k), f j = ∑ i ∈ range k, ∑ j ∈ Ico (blk i) (blk (i + 1)), f j := by
  induction k with
  | zero => simp [blk]
  | succ k ih => rw [sum_range_succ, ← ih, sum_range_add_sum_Ico _ (blk_mono (Nat.le_succ k))]

lemma log_blk (i : ℕ) (hi : 1 ≤ i) : Real.log (blk i : ℝ) = 2 ^ i * Real.log 2 := by
  simp only [blk, if_neg (show i ≠ 0 by omega)]
  push_cast
  rw [Real.log_pow]
  push_cast; ring

lemma blk_ge (i : ℕ) (hi : 1 ≤ i) : 4 ≤ blk i := by
  simp only [blk, if_neg (show i ≠ 0 by omega)]
  calc 4 = 2 ^ (2 ^ 1) := by norm_num
    _ ≤ 2 ^ (2 ^ i) := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hi)

lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

lemma sum_two_pow_succ_le (k : ℕ) : ∑ i ∈ range k, (2:ℝ) ^ (i + 1) ≤ 2 ^ (k + 1) := by
  have : ∀ k : ℕ, ∑ i ∈ range k, (2:ℝ) ^ (i + 1) + 2 = 2 ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ]; rw [pow_succ 2 (k + 1)]; linarith
  linarith [this k]

/-- Abstract form of the Kraft necessity (Hilbert blocks, §3.2). -/
theorem core_kraft (α β : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j) (hβ : ∀ k, 0 ≤ β k)
    (hβ2 : Summable (fun k => β k ^ 2))
    (hid : ∀ m, 1 ≤ ∑ j ∈ range (m + 1), α j * β (m - j))
    (g : ℝ → ℝ) (hg1 : ∀ u, 1 ≤ u → 1 ≤ g u) (hgm : MonotoneOn g (Set.Ici 1)) (C : ℝ)
    (hC : ∀ t : ℕ, 3 ≤ t →
      ∑ j ∈ range t, α j ^ 2 ≤ C * (Real.log (t:ℝ)) ^ 2 * g (Real.log (t:ℝ))) :
    Summable (fun k : ℕ => 1 / g (2 ^ k)) := by
  set χ := chi β with hχ
  set A : ℕ → ℝ := fun i => ∑ j ∈ Ico (blk i) (blk (i + 1)), χ j ^ 2 with hAdef
  set S : ℕ → ℝ := fun i => ∑ j ∈ Ico (blk i) (blk (i + 1)), α j * χ j with hSdef
  set Q := ∑' k, β k ^ 2 with hQ
  have hA0 : ∀ i, 0 ≤ A i := fun i => sum_nonneg (fun j _ => sq_nonneg _)
  have hS0 : ∀ i, 0 ≤ S i := fun i => sum_nonneg (fun j _ => mul_nonneg (hα j) (chi_nonneg β hβ j))
  have hgpos : ∀ u, 1 ≤ u → 0 < g u := fun u hu => lt_of_lt_of_le one_pos (hg1 u hu)
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hC0 : 0 ≤ C := by
    have h3 := hC 3 le_rfl
    have hE : 0 ≤ ∑ j ∈ range 3, α j ^ 2 := sum_nonneg (fun j _ => sq_nonneg _)
    have hl3 := one_lt_log_three
    have hX : 0 < (Real.log ((3:ℕ):ℝ)) ^ 2 * g (Real.log ((3:ℕ):ℝ)) := by
      push_cast
      have := hgpos (Real.log 3) hl3.le
      positivity
    have : 0 ≤ C * ((Real.log ((3:ℕ):ℝ)) ^ 2 * g (Real.log ((3:ℕ):ℝ))) := by
      rw [← mul_assoc]; linarith
    exact (mul_nonneg_iff_of_pos_right hX).mp this
  -- the key per-scale estimate
  have key : ∀ k : ℕ, 1 ≤ k →
      1 / g (2 ^ k) * 2 ^ k ≤ 2 * C * ∑ i ∈ range k, (2:ℝ) ^ (i + 1) * A i := by
    intro k hk
    have hgk : 0 < g (2 ^ k) := hgpos _ (one_le_pow₀ (by norm_num))
    have hlogk : (2:ℝ) ^ k * Real.log 2 ≤ ∑ i ∈ range k, S i := by
      rw [← log_blk k hk]
      have h1 := log_le_sum_chi α β hα hβ hβ2 hid (blk k)
      have h2 : Real.log (blk k : ℝ) ≤ Real.log ((blk k : ℝ) + 1) := by
        have : (0:ℝ) < blk k := by have := blk_ge k hk; exact_mod_cast (by omega : 0 < blk k)
        exact Real.log_le_log this (by linarith)
      rw [sum_blocks] at h1
      exact h2.trans h1
    have hSi : ∀ i ∈ range k,
        S i ^ 2 ≤ C * (Real.log 2) ^ 2 * g (2 ^ k) * ((2:ℝ) ^ (i + 1)) ^ 2 * A i := by
      intro i hi
      have hik : i + 1 ≤ k := mem_range.mp hi
      have hcs := sum_mul_sq_le_sq_mul_sq (Ico (blk i) (blk (i + 1))) α χ
      have hE : ∑ j ∈ Ico (blk i) (blk (i + 1)), α j ^ 2 ≤
          C * (2 ^ (i + 1) * Real.log 2) ^ 2 * g (2 ^ k) := by
        have h1 : ∑ j ∈ Ico (blk i) (blk (i + 1)), α j ^ 2 ≤ ∑ j ∈ range (blk (i + 1)), α j ^ 2 := by
          rw [← sum_range_add_sum_Ico _ (blk_mono (Nat.le_succ i))]
          have : 0 ≤ ∑ j ∈ range (blk i), α j ^ 2 := sum_nonneg (fun j _ => sq_nonneg _)
          linarith
        have h2 := hC (blk (i + 1)) (by have := blk_ge (i + 1) (by omega); omega)
        rw [log_blk (i + 1) (by omega)] at h2
        have hu1 : (1:ℝ) ≤ 2 ^ (i + 1) * Real.log 2 := by
          have : (2:ℝ) ≤ 2 ^ (i + 1) := by
            calc (2:ℝ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (i + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
          nlinarith
        have hu2 : (2:ℝ) ^ (i + 1) * Real.log 2 ≤ 2 ^ k := by
          have : (2:ℝ) ^ (i + 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hik
          have : (0:ℝ) < 2 ^ (i + 1) := by positivity
          nlinarith
        have h3 : g (2 ^ (i + 1) * Real.log 2) ≤ g (2 ^ k) :=
          hgm (Set.mem_Ici.mpr hu1) (Set.mem_Ici.mpr (hu1.trans hu2)) hu2
        calc _ ≤ _ := h1
          _ ≤ _ := h2
          _ ≤ C * (2 ^ (i + 1) * Real.log 2) ^ 2 * g (2 ^ k) := by gcongr
      calc S i ^ 2 ≤ (∑ j ∈ Ico (blk i) (blk (i + 1)), α j ^ 2) * A i := hcs
        _ ≤ (C * (2 ^ (i + 1) * Real.log 2) ^ 2 * g (2 ^ k)) * A i :=
            mul_le_mul_of_nonneg_right hE (hA0 i)
        _ = C * (Real.log 2) ^ 2 * g (2 ^ k) * ((2:ℝ) ^ (i + 1)) ^ 2 * A i := by ring
    have hcs2 : (∑ i ∈ range k, S i) ^ 2 ≤
        (∑ i ∈ range k, (2:ℝ) ^ (i + 1)) * ∑ i ∈ range k, S i ^ 2 / 2 ^ (i + 1) := by
      apply sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro i _; positivity
      · intro i _; have := hS0 i; positivity
      · intro i _
        apply le_of_eq
        field_simp
    have hW : ∑ i ∈ range k, S i ^ 2 / 2 ^ (i + 1) ≤
        C * (Real.log 2) ^ 2 * g (2 ^ k) * ∑ i ∈ range k, (2:ℝ) ^ (i + 1) * A i := by
      rw [mul_sum]
      apply sum_le_sum
      intro i hi
      have := hSi i hi
      rw [div_le_iff₀ (by positivity)]
      calc S i ^ 2 ≤ C * (Real.log 2) ^ 2 * g (2 ^ k) * ((2:ℝ) ^ (i + 1)) ^ 2 * A i := this
        _ = _ := by ring
    have hWnn : 0 ≤ ∑ i ∈ range k, (2:ℝ) ^ (i + 1) * A i :=
      sum_nonneg (fun i _ => mul_nonneg (by positivity) (hA0 i))
    have hfin : ((2:ℝ) ^ k * Real.log 2) ^ 2 ≤
        2 ^ (k + 1) * (C * (Real.log 2) ^ 2 * g (2 ^ k) * ∑ i ∈ range k, (2:ℝ) ^ (i + 1) * A i) := by
      have h1 : ((2:ℝ) ^ k * Real.log 2) ^ 2 ≤ (∑ i ∈ range k, S i) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hlogk 2
      have h2 : (∑ i ∈ range k, (2:ℝ) ^ (i + 1)) * ∑ i ∈ range k, S i ^ 2 / 2 ^ (i + 1) ≤
          2 ^ (k + 1) * (C * (Real.log 2) ^ 2 * g (2 ^ k) * ∑ i ∈ range k, (2:ℝ) ^ (i + 1) * A i) := by
        apply mul_le_mul (sum_two_pow_succ_le k) hW
        · exact sum_nonneg (fun i _ => by have := hS0 i; positivity)
        · positivity
      linarith
    -- simplify
    set W := ∑ i ∈ range k, (2:ℝ) ^ (i + 1) * A i
    have hl2pos : 0 < (Real.log 2) ^ 2 := by positivity
    have h2k : (0:ℝ) < 2 ^ k := by positivity
    have e1 : ((2:ℝ) ^ k * Real.log 2) ^ 2 = (2 ^ k * 2 ^ k) * (Real.log 2) ^ 2 := by ring
    have e2 : (2:ℝ) ^ (k + 1) * (C * (Real.log 2) ^ 2 * g (2 ^ k) * W) =
        (2 ^ k * (2 * C * g (2 ^ k) * W)) * (Real.log 2) ^ 2 := by rw [pow_succ]; ring
    rw [e1, e2] at hfin
    have h3 := le_of_mul_le_mul_right hfin hl2pos
    have h4 : (2:ℝ) ^ k ≤ 2 * C * g (2 ^ k) * W := le_of_mul_le_mul_left h3 h2k
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hgk]
    calc (2:ℝ) ^ k ≤ 2 * C * g (2 ^ k) * W := h4
      _ = 2 * C * W * g (2 ^ k) := by ring
  -- summing over scales
  have hbound : ∀ K : ℕ, ∑ k ∈ range (K + 1), 1 / g (2 ^ k) ≤ 1 + 4 * C * (16 * Q) := by
    intro K
    rw [← sum_range_add_sum_Ico _ (by omega : 1 ≤ K + 1)]
    have h0 : ∑ k ∈ range 1, 1 / g ((2:ℝ) ^ k) ≤ 1 := by
      simp only [sum_range_one, pow_zero]
      rw [div_le_one (hgpos 1 le_rfl)]; exact hg1 1 le_rfl
    have hstep : ∀ k ∈ Ico 1 (K + 1), 1 / g ((2:ℝ) ^ k) ≤
        ∑ i ∈ range k, 2 * C * ((2:ℝ) ^ (i + 1) / 2 ^ k) * A i := by
      intro k hk
      have hk1 : 1 ≤ k := (mem_Ico.mp hk).1
      have h := key k hk1
      have h2k : (0:ℝ) < 2 ^ k := by positivity
      rw [← le_div_iff₀ h2k] at h
      refine h.trans (le_of_eq ?_)
      rw [mul_sum, sum_div]
      apply sum_congr rfl; intro i _; ring
    have hswap : ∑ k ∈ Ico 1 (K + 1), ∑ i ∈ range k, 2 * C * ((2:ℝ) ^ (i + 1) / 2 ^ k) * A i =
        ∑ i ∈ range K, ∑ k ∈ Ico (i + 1) (K + 1), 2 * C * ((2:ℝ) ^ (i + 1) / 2 ^ k) * A i := by
      apply sum_comm'
      intro k i
      simp only [mem_Ico, mem_range]
      omega
    have hgeo : ∀ i : ℕ, ∑ k ∈ Ico (i + 1) (K + 1), 2 * C * ((2:ℝ) ^ (i + 1) / 2 ^ k) * A i ≤
        4 * C * A i := by
      intro i
      have hg : ∑ k ∈ Ico (i + 1) (K + 1), ((1:ℝ) / 2) ^ k ≤ ((1:ℝ) / 2) ^ (i + 1) / (1 - 1 / 2) :=
        geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
      have e : ∑ k ∈ Ico (i + 1) (K + 1), 2 * C * ((2:ℝ) ^ (i + 1) / 2 ^ k) * A i =
          (2 * C * 2 ^ (i + 1) * A i) * ∑ k ∈ Ico (i + 1) (K + 1), ((1:ℝ) / 2) ^ k := by
        rw [mul_sum]; apply sum_congr rfl; intro k _
        rw [div_pow, one_pow]; field_simp
      rw [e]
      have hc : 0 ≤ 2 * C * 2 ^ (i + 1) * A i := by have := hA0 i; positivity
      calc (2 * C * 2 ^ (i + 1) * A i) * ∑ k ∈ Ico (i + 1) (K + 1), ((1:ℝ) / 2) ^ k
          ≤ (2 * C * 2 ^ (i + 1) * A i) * (((1:ℝ) / 2) ^ (i + 1) / (1 - 1 / 2)) :=
            mul_le_mul_of_nonneg_left hg hc
        _ = 4 * C * A i := by
            rw [div_pow, one_pow]; field_simp; ring
    have hAsum : ∑ i ∈ range K, A i ≤ 16 * Q := by
      have := sum_blocks (fun j => χ j ^ 2) K
      rw [← this]
      exact chi_sq_sum_le β hβ hβ2 _
    calc ∑ k ∈ range 1, 1 / g ((2:ℝ) ^ k) + ∑ k ∈ Ico 1 (K + 1), 1 / g ((2:ℝ) ^ k)
        ≤ 1 + ∑ k ∈ Ico 1 (K + 1), ∑ i ∈ range k, 2 * C * ((2:ℝ) ^ (i + 1) / 2 ^ k) * A i :=
          add_le_add h0 (sum_le_sum hstep)
      _ = 1 + ∑ i ∈ range K, ∑ k ∈ Ico (i + 1) (K + 1), 2 * C * ((2:ℝ) ^ (i + 1) / 2 ^ k) * A i := by
          rw [hswap]
      _ ≤ 1 + ∑ i ∈ range K, 4 * C * A i := by gcongr with i _; exact hgeo i
      _ = 1 + 4 * C * ∑ i ∈ range K, A i := by rw [mul_sum]
      _ ≤ 1 + 4 * C * (16 * Q) := by gcongr
  have hnn : ∀ k : ℕ, 0 ≤ 1 / g ((2:ℝ) ^ k) := fun k =>
    le_of_lt (one_div_pos.mpr (hgpos _ (one_le_pow₀ (by norm_num))))
  refine summable_of_sum_range_le (c := 1 + 4 * C * (16 * Q)) hnn (fun n => ?_)
  calc ∑ k ∈ range n, 1 / g ((2:ℝ) ^ k) ≤ ∑ k ∈ range (n + 1), 1 / g ((2:ℝ) ^ k) := by
        rw [sum_range_succ]; linarith [hnn n]
    _ ≤ _ := hbound n



end PCCKraftCore

theorem solution (α β : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j) (hβ : ∀ k, 0 ≤ β k)
    (hβ2 : Summable (fun k => β k ^ 2))
    (hconv : ∀ m : ℕ, 1 ≤ ∑ j ∈ Finset.range (m + 1), α j * β (m - j))
    (g : ℝ → ℝ) (hg1 : ∀ u : ℝ, 1 ≤ u → 1 ≤ g u) (hgm : MonotoneOn g (Set.Ici 1)) (C : ℝ)
    (hC : ∀ t : ℕ, 3 ≤ t →
      ∑ j ∈ Finset.range t, α j ^ 2 ≤ C * (Real.log (t : ℝ)) ^ 2 * g (Real.log (t : ℝ))) :
    Summable (fun k : ℕ => 1 / g ((2 : ℝ) ^ k)) :=
  PCCKraftCore.core_kraft α β hα hβ hβ2 hconv g hg1 hgm C hC
