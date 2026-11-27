-- Prove2me | solution 1 for PrivateContinualCounting.Kraft.fixed_period
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:45:03.006979+00:00
-- url     : https://prove2.me/submissions/1657e2e1-a036-4c83-a837-f84746686143

import Theorems.Thm_PrivateContinualCounting_Kraft_hilbert_log_divergence
import Definitions.Def_PrivateContinualCounting_Kraft_PeriodicCounter

set_option autoImplicit false

open Finset Filter Topology

namespace PCCKraftPer
open PrivateContinualCounting.Kraft

lemma l2_summable {I : Type} (f : I → ℝ) (h : Memℓp f 2) : Summable (fun i => f i ^ 2) := by
  have := (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).1 h
  simpa [Real.norm_eq_abs, sq_abs] using this

lemma summable_mul_of_sq {I : Type} (x y : I → ℝ) (hx : Summable (fun i => x i ^ 2))
    (hy : Summable (fun i => y i ^ 2)) : Summable (fun i => x i * y i) := by
  refine Summable.of_norm_bounded (hx.add hy) (fun i => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|x i| - |y i|), sq_abs (x i), sq_abs (y i)]

lemma tsum_cs {I : Type} (x y : I → ℝ) (hx : Summable (fun i => x i ^ 2))
    (hy : Summable (fun i => y i ^ 2)) :
    |∑' i, x i * y i| ≤ Real.sqrt (∑' i, x i ^ 2) * Real.sqrt (∑' i, y i ^ 2) := by
  have hxa : Summable (fun i => |x i| ^ (2:ℝ)) := by simpa [Real.rpow_two, sq_abs] using hx
  have hya : Summable (fun i => |y i| ^ (2:ℝ)) := by simpa [Real.rpow_two, sq_abs] using hy
  have hH := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (fun i => abs_nonneg (x i)) (fun i => abs_nonneg (y i)) hxa hya
  have hxy := summable_mul_of_sq x y hx hy
  have h1 : |∑' i, x i * y i| ≤ ∑' i, |x i| * |y i| := by
    have := norm_tsum_le_tsum_norm hxy.norm
    simpa [Real.norm_eq_abs, abs_mul] using this
  refine h1.trans (le_of_eq_of_le ?_ hH |>.trans (le_of_eq ?_))
  · rfl
  · simp only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow]

section
variable {p : ℕ} {I₀ : Type} [Countable I₀] (M : PeriodicCounter p I₀)

lemma R_col0 (b' : ℕ) (i : I₀) :
    M.counter.factors.R (b', i) 0 = M.Rblock b' i ⟨0, M.positive_period⟩ := by
  have := M.strategy_toeplitz b' i 0 ⟨0, M.positive_period⟩
  simpa using this

lemma L_fiber_summable (j : ℕ) (a : Fin p) : Summable (fun i => M.Lblock j a i ^ 2) := by
  have h := l2_summable _ (M.counter.factors.rows_l2 (p * j + a.val))
  have h2 := h.comp_injective (i := fun i : I₀ => ((0:ℕ), i)) (fun i i' hii => by simpa using hii)
  refine h2.congr (fun i => ?_)
  show M.counter.factors.L (p * j + a.val) (0, i) ^ 2 = M.Lblock j a i ^ 2
  rw [M.decoder_toeplitz]
  simp

lemma R_col0_summable :
    Summable (fun x : ℕ × I₀ => M.Rblock x.1 x.2 ⟨0, M.positive_period⟩ ^ 2) := by
  have h := l2_summable _ (M.counter.factors.cols_l2 0)
  refine h.congr (fun x => ?_)
  obtain ⟨b', i⟩ := x
  rw [R_col0]

/-- The column energy `Σ_k ‖r_k‖²` of input phase `0`. -/
noncomputable def beta (k : ℕ) : ℝ :=
  Real.sqrt (∑' i, M.Rblock k i ⟨0, M.positive_period⟩ ^ 2)

noncomputable def alpha (a : Fin p) (j : ℕ) : ℝ := Real.sqrt (∑' i, M.Lblock j a i ^ 2)

lemma beta_sq (k : ℕ) : beta M k ^ 2 = ∑' i, M.Rblock k i ⟨0, M.positive_period⟩ ^ 2 :=
  Real.sq_sqrt (tsum_nonneg (fun i => sq_nonneg _))

lemma alpha_sq (a : Fin p) (j : ℕ) : alpha M a j ^ 2 = ∑' i, M.Lblock j a i ^ 2 :=
  Real.sq_sqrt (tsum_nonneg (fun i => sq_nonneg _))

lemma beta_sq_summable : Summable (fun k => beta M k ^ 2) := by
  simp_rw [beta_sq]
  exact (R_col0_summable M).prod

lemma beta_sq_tsum : ∑' k, beta M k ^ 2 =
    ∑' x : ℕ × I₀, M.Rblock x.1 x.2 ⟨0, M.positive_period⟩ ^ 2 := by
  simp_rw [beta_sq]
  exact ((R_col0_summable M).tsum_prod).symm

lemma conv_identity (a : Fin p) (m : ℕ) :
    ∑ j ∈ range (m + 1), ∑' i, M.Lblock j a i * M.Rblock (m - j) i ⟨0, M.positive_period⟩ = 1 := by
  set z : Fin p := ⟨0, M.positive_period⟩
  have hprod := M.counter.factors.product (p * m + a.val) 0
  rw [if_pos (Nat.zero_le _)] at hprod
  set f : ℕ × I₀ → ℝ := fun x => M.counter.factors.L (p * m + a.val) x *
    M.counter.factors.R x 0 with hf
  have hfs : Summable f :=
    summable_mul_of_sq _ _ (l2_summable _ (M.counter.factors.rows_l2 _))
      (l2_summable _ (M.counter.factors.cols_l2 0))
  have hf' : ∀ b' i, f (b', i) = (if b' ≤ m then M.Lblock (m - b') a i else 0) * M.Rblock b' i z := by
    intro b' i
    rw [hf]
    dsimp only
    rw [M.decoder_toeplitz, R_col0]
  rw [hfs.tsum_prod] at hprod
  have hzero : ∀ b' ∉ range (m + 1), ∑' i, f (b', i) = 0 := by
    intro b' hb
    have : ¬ b' ≤ m := by simpa [Nat.lt_succ_iff] using hb
    simp [hf', this]
  rw [tsum_eq_sum hzero] at hprod
  rw [← hprod, ← sum_range_reflect]
  apply sum_congr rfl
  intro j hj
  have hj' : j < m + 1 := mem_range.mp hj
  apply tsum_congr
  intro i
  rw [hf']
  have h1 : j ≤ m := by omega
  rw [if_pos h1]
  have h3 : m + 1 - 1 - j = m - j := by omega
  have h2 : m - (m - j) = j := by omega
  rw [h3, h2]

lemma alpha_beta_identity (a : Fin p) (m : ℕ) :
    1 ≤ ∑ j ∈ range (m + 1), alpha M a j * beta M (m - j) := by
  rw [← conv_identity M a m]
  apply sum_le_sum
  intro j _
  refine (le_abs_self _).trans ?_
  have := tsum_cs (fun i => M.Lblock j a i) (fun i => M.Rblock (m - j) i ⟨0, M.positive_period⟩)
    (L_fiber_summable M j a) ((R_col0_summable M).prod_factor (m - j))
  simpa [alpha, beta] using this

theorem phase_diverges (a : Fin p) : LogSqDiverges (M.phaseEnergy a) := by
  have h := hilbert_log_divergence (alpha M a) (beta M) (fun j => Real.sqrt_nonneg _)
    (fun k => Real.sqrt_nonneg _) (beta_sq_summable M) (alpha_beta_identity M a)
  unfold LogSqDiverges
  refine h.congr (fun n => ?_)
  simp [PeriodicCounter.phaseEnergy, alpha_sq]

lemma row_energy (b : ℕ) (a : Fin p) :
    ∑' x, M.counter.factors.L (p * b + a.val) x ^ 2 = M.phaseEnergy a (b + 1) := by
  have hs := l2_summable _ (M.counter.factors.rows_l2 (p * b + a.val))
  rw [hs.tsum_prod]
  have hf' : ∀ b' i, M.counter.factors.L (p * b + a.val) (b', i) ^ 2 =
      if b' ≤ b then M.Lblock (b - b') a i ^ 2 else 0 := by
    intro b' i
    rw [M.decoder_toeplitz]
    split_ifs <;> simp
  have hzero : ∀ b' ∉ range (b + 1), ∑' i, M.counter.factors.L (p * b + a.val) (b', i) ^ 2 = 0 := by
    intro b' hb
    have : ¬ b' ≤ b := by simpa [Nat.lt_succ_iff] using hb
    simp [hf', this]
  rw [tsum_eq_sum hzero, PeriodicCounter.phaseEnergy, ← sum_range_reflect]
  apply sum_congr rfl
  intro j hj
  have hj' : j < b + 1 := mem_range.mp hj
  apply tsum_congr
  intro i
  rw [hf', if_pos (by omega)]
  have h3 : b + 1 - 1 - j = b - j := by omega
  have h2 : b - (b - j) = j := by omega
  rw [h3, h2]

lemma beta_tsum_le_deltaSq : ∑' k, beta M k ^ 2 ≤ M.counter.factors.deltaSq := by
  rw [beta_sq_tsum]
  have h := le_csSup M.counter.factors.bounded_sensitivity (Set.mem_range_self 0)
  refine le_of_eq_of_le ?_ h
  apply tsum_congr
  intro x
  obtain ⟨b', i⟩ := x
  rw [R_col0]

lemma beta_tsum_pos : 0 < ∑' k, beta M k ^ 2 := by
  have z : Fin p := ⟨0, M.positive_period⟩
  have h0 := alpha_beta_identity M z 0
  simp only [zero_add, sum_range_one, Nat.sub_zero] at h0
  have hb : 0 < beta M 0 := by
    by_contra h
    have : beta M 0 = 0 := le_antisymm (not_lt.mp h) (Real.sqrt_nonneg _)
    rw [this, mul_zero] at h0
    linarith
  exact lt_of_lt_of_le (by positivity)
    ((beta_sq_summable M).le_tsum 0 (fun k _ => sq_nonneg _))

lemma phaseEnergy_nonneg (a : Fin p) (n : ℕ) : 0 ≤ M.phaseEnergy a n :=
  sum_nonneg (fun d _ => tsum_nonneg (fun i => sq_nonneg _))

lemma variance_ge (t : ℕ) (ht : 1 ≤ t) :
    (∑' k, beta M k ^ 2) *
      M.phaseEnergy ⟨(t - 1) % p, Nat.mod_lt _ M.positive_period⟩ ((t - 1) / p + 1) ≤
      M.counter.variance t := by
  have hdecomp : t - 1 = p * ((t - 1) / p) + ((t - 1) % p) := (Nat.div_add_mod (t - 1) p).symm
  unfold GaussianCounter.variance
  rw [if_neg (by omega)]
  have hrow := row_energy M ((t - 1) / p) ⟨(t - 1) % p, Nat.mod_lt _ M.positive_period⟩
  simp only at hrow
  rw [← hdecomp] at hrow
  rw [hrow]
  exact mul_le_mul_of_nonneg_right (beta_tsum_le_deltaSq M) (phaseEnergy_nonneg M _ _)

/-- Lemma A.1: fixed-period counters. -/
theorem fixed_period_diverges : LogSqDiverges M.counter.variance := by
  have hp := M.positive_period
  set Δ0 := ∑' k, beta M k ^ 2 with hΔ0
  have hΔ0 : 0 < Δ0 := beta_tsum_pos M
  unfold LogSqDiverges
  rw [tendsto_atTop]
  intro K
  set K' := max K 1 with hK'
  have hK'pos : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- all phases at once
  have hall : ∀ᶠ n in atTop, ∀ a : Fin p,
      4 * K' / Δ0 ≤ M.phaseEnergy a n / (Real.log n) ^ 2 := by
    rw [Filter.eventually_all]
    intro a
    exact (tendsto_atTop.1 (phase_diverges M a)) _
  have hn : Tendsto (fun t : ℕ => (t - 1) / p + 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨p * N + 1, fun t ht => ?_⟩
    have : N ≤ (t - 1) / p := by
      rw [Nat.le_div_iff_mul_le hp]
      have : p * N ≤ t - 1 := by omega
      linarith [mul_comm p N]
    omega
  have hlogn := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)).eventually_ge_atTop
    (max (Real.log p) 1)
  filter_upwards [hn.eventually hall, hlogn, eventually_ge_atTop 2] with t h1 h2 ht2
  simp only [Function.comp] at h2
  set n := (t - 1) / p + 1 with hndef
  set a : Fin p := ⟨(t - 1) % p, Nat.mod_lt _ hp⟩ with hadef
  have hvar := variance_ge M t (by omega)
  have hb := h1 a
  set E := M.phaseEnergy a n
  set Ln := Real.log (n:ℝ)
  set Lt := Real.log (t:ℝ)
  have hLn1 : 1 ≤ Ln := le_trans (le_max_right _ _) h2
  have hLnp : Real.log p ≤ Ln := le_trans (le_max_left _ _) h2
  have htn : (t:ℝ) ≤ p * n := by
    have hdecomp : t - 1 = p * ((t - 1) / p) + ((t - 1) % p) := (Nat.div_add_mod (t - 1) p).symm
    have hmod : (t - 1) % p < p := Nat.mod_lt _ hp
    have : t ≤ p * n := by
      rw [hndef, mul_add, mul_one]; omega
    exact_mod_cast this
  have hLt0 : 0 < Lt := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  have hLt : Lt ≤ 2 * Ln := by
    have hp0 : (0:ℝ) < p := by exact_mod_cast hp
    have hn0 : (0:ℝ) < n := by positivity
    have := Real.log_le_log (by positivity) htn
    rw [Real.log_mul hp0.ne' hn0.ne'] at this
    linarith
  have hLn0 : 0 < Ln := by linarith
  have hE : 4 * K' / Δ0 * Ln ^ 2 ≤ E := by
    rwa [le_div_iff₀ (by positivity)] at hb
  rw [le_div_iff₀ (by positivity)]
  have hE0 : 0 ≤ E := phaseEnergy_nonneg M a n
  calc K * Lt ^ 2 ≤ K' * Lt ^ 2 := by gcongr; exact le_max_left _ _
    _ ≤ K' * (4 * Ln ^ 2) := by
        gcongr
        nlinarith
    _ = Δ0 * (4 * K' / Δ0 * Ln ^ 2) := by field_simp
    _ ≤ Δ0 * E := by gcongr
    _ ≤ M.counter.variance t := hvar

end

end PCCKraftPer

open PrivateContinualCounting.Kraft in
theorem solution (p : ℕ) (I₀ : Type) [Countable I₀] (M : PeriodicCounter p I₀) :
    LogSqDiverges M.counter.variance :=
  PCCKraftPer.fixed_period_diverges M
