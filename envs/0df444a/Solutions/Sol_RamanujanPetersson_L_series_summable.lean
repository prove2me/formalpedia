-- Prove2me | solution 1 for RamanujanPetersson.L_series_summable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:56:28.213964+00:00
-- url     : https://prove2.me/submissions/4e449d00-9a5c-4d3c-bbb2-683153c451ec

import Definitions.Def_RamanujanPetersson_tau
import Mathlib

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups Complex MeasureTheory
open scoped Real

namespace RPL2

local notation "𝕢" => Function.Periodic.qParam

noncomputable abbrev D : CuspForm 𝒮ℒ 12 := CuspForm.discriminant

noncomputable def g {t : ℝ} (ht : 0 < t) (u : ℝ) : ℂ := D ⟨u + t * Complex.I, by simpa using ht⟩

lemma g_cont {t : ℝ} (ht : 0 < t) : Continuous (g ht) := by
  unfold g
  fun_prop

lemma coeff_eq (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (qExpansion 1 ModularForm.discriminant).coeff n =
      ∫ u in (0:ℝ)..1, 1 / 𝕢 1 (u + t * Complex.I) ^ n * g ht u := by
  have := ModularFormClass.qExpansion_coeff_eq_intervalIntegral (Γ := 𝒮ℒ) (k := 12) (f := D)
    one_pos one_mem_strictPeriods_SL n ht
  rw [show (⇑D : ℍ → ℂ) = ModularForm.discriminant from rfl] at this
  rw [this]
  simp only [g, one_div, inv_one, one_mul, Complex.ofReal_one]
  rfl

lemma kernel (n : ℕ) (t u : ℝ) :
    1 / 𝕢 1 (u + t * Complex.I) ^ n = Real.exp (2 * π * n * t) *
      fourier (-(n : ℤ)) (u : AddCircle ((1:ℝ) - 0)) := by
  rw [fourier_coe_apply, Function.Periodic.qParam, ← Complex.exp_nat_mul, one_div, ← Complex.exp_neg,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma coeff_fourier (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (qExpansion 1 ModularForm.discriminant).coeff n =
      Real.exp (2 * π * n * t) * fourierCoeffOn zero_lt_one (g ht) n := by
  rw [coeff_eq n ht, fourierCoeffOn_eq_integral]
  simp_rw [kernel n t]
  simp only [sub_zero, ne_eq, one_ne_zero, not_false_eq_true, div_self, one_smul, smul_eq_mul]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext u
  ring


lemma exists_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ {t : ℝ} (ht : 0 < t) (u : ℝ), ‖g ht u‖ ≤ C / t ^ 6 := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound (Γ := 𝒮ℒ) D
  refine ⟨max C 0, le_max_right _ _, fun {t} ht u => ?_⟩
  have h := hC ⟨u + t * Complex.I, by simpa using ht⟩
  have him : (⟨u + t * Complex.I, by simpa using ht⟩ : ℍ).im = t := by simp [UpperHalfPlane.im]
  rw [him, show ((12 : ℤ) : ℝ) / 2 = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
  exact h.trans (by gcongr; exact le_max_left _ _)

lemma l2_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ {t : ℝ}, 0 < t → ∀ N : ℕ,
    ∑ m ∈ Finset.range (N + 1),
      ‖(qExpansion 1 ModularForm.discriminant).coeff m‖ ^ 2 * Real.exp (-(4 * π * m * t))
      ≤ C ^ 2 / t ^ 12 := by
  obtain ⟨C, hC0, hC⟩ := exists_bound
  refine ⟨C, hC0, fun {t} ht N => ?_⟩
  have hmem : MemLp (g ht) 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    MemLp.of_bound (g_cont ht).aestronglyMeasurable (C / t ^ 6) (ae_of_all _ (hC ht))
  have hs := hasSum_sq_fourierCoeffOn zero_lt_one hmem
  have hint : ∫ x in (0:ℝ)..1, ‖g ht x‖ ^ 2 ≤ (C / t ^ 6) ^ 2 := by
    have := intervalIntegral.integral_mono_on (a := 0) (b := 1) zero_le_one
      (f := fun x => ‖g ht x‖ ^ 2) (g := fun _ => (C / t ^ 6) ^ 2)
      (((g_cont ht).norm.pow 2).intervalIntegrable (μ := volume) 0 1)
      (continuous_const.intervalIntegrable (μ := volume) 0 1)
      (fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hC ht x) 2)
    simpa using this
  have hle := sum_le_hasSum ((Finset.range (N + 1)).map Nat.castEmbedding)
    (fun i _ => sq_nonneg _) hs
  rw [Finset.sum_map] at hle
  calc _ = ∑ m ∈ Finset.range (N + 1), ‖fourierCoeffOn zero_lt_one (g ht) (Nat.castEmbedding m)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [coeff_fourier m ht, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
          ← Real.exp_nat_mul]
        rw [mul_comm, ← mul_assoc, ← Real.exp_add]
        simp only [Nat.castEmbedding_apply]
        have : -(4 * π * m * t) + ((2:ℕ):ℝ) * (2 * π * m * t) = 0 := by push_cast; ring
        rw [this, Real.exp_zero, one_mul]
    _ ≤ _ := hle
    _ ≤ (C / t ^ 6) ^ 2 := by simpa using hint
    _ = C ^ 2 / t ^ 12 := by rw [div_pow, ← pow_mul]


lemma sq_sum_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
    ∑ m ∈ Finset.range (N + 1), ‖(qExpansion 1 ModularForm.discriminant).coeff m‖ ^ 2
      ≤ K * (N : ℝ) ^ 12 := by
  obtain ⟨C, hC0, hC⟩ := l2_bound
  refine ⟨Real.exp (4 * π) * C ^ 2, by positivity, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : (0 : ℝ) < 1 / N := by positivity
  have h := hC ht N
  have key : ∀ m ∈ Finset.range (N + 1),
      ‖(qExpansion 1 ModularForm.discriminant).coeff m‖ ^ 2 ≤ Real.exp (4 * π) *
        (‖(qExpansion 1 ModularForm.discriminant).coeff m‖ ^ 2 *
          Real.exp (-(4 * π * m * (1 / N)))) := by
    intro m hm
    have hmN : (m : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [mul_left_comm, ← Real.exp_add]
    refine le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp ?_)
    have : (m : ℝ) * (1 / N) ≤ 1 := by rw [mul_one_div]; exact (div_le_one hNpos).mpr hmN
    nlinarith [Real.pi_pos]
  calc _ ≤ ∑ m ∈ Finset.range (N + 1), Real.exp (4 * π) *
        (‖(qExpansion 1 ModularForm.discriminant).coeff m‖ ^ 2 *
          Real.exp (-(4 * π * m * (1 / N)))) := Finset.sum_le_sum key
    _ = Real.exp (4 * π) * ∑ m ∈ Finset.range (N + 1),
        (‖(qExpansion 1 ModularForm.discriminant).coeff m‖ ^ 2 *
          Real.exp (-(4 * π * m * (1 / N)))) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (4 * π) * (C ^ 2 / (1 / N) ^ 12) := by gcongr
    _ = _ := by field_simp

lemma abs_sum_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
    ∑ k ∈ Finset.Icc 1 N, ‖(qExpansion 1 ModularForm.discriminant).coeff k‖
      ≤ K * (N : ℝ) ^ ((13 : ℝ) / 2) := by
  obtain ⟨K, hK0, hK⟩ := sq_sum_bound
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set a := fun k : ℕ => ‖(qExpansion 1 ModularForm.discriminant).coeff k‖
  have hsub : Finset.Icc 1 N ⊆ Finset.range (N + 1) := by
    intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N) (fun _ => (1 : ℝ)) a
  simp only [one_mul, one_pow, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one,
    add_tsub_cancel_right] at hcs
  have h2 : ∑ k ∈ Finset.Icc 1 N, a k ^ 2 ≤ K * (N : ℝ) ^ 12 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans (hK N hN)
  have hS0 : 0 ≤ ∑ k ∈ Finset.Icc 1 N, a k := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hR0 : 0 ≤ Real.sqrt K * (N : ℝ) ^ ((13 : ℝ) / 2) := by positivity
  refine (pow_le_pow_iff_left₀ hS0 hR0 two_ne_zero).mp ?_
  calc _ ≤ (N : ℝ) * ∑ k ∈ Finset.Icc 1 N, a k ^ 2 := hcs
    _ ≤ N * (K * (N : ℝ) ^ 12) := by gcongr
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt hK0, ← Real.rpow_natCast ((N : ℝ) ^ ((13 : ℝ) / 2)) 2,
        ← Real.rpow_mul hNpos.le]
      norm_num
      ring

end RPL2

namespace RPL2

lemma tau_sum_isBigO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖RamanujanPetersson.tau k‖) =O[Filter.atTop]
    fun n : ℕ => (n : ℝ) ^ ((13 : ℝ) / 2) := by
  obtain ⟨K, hK0, hK⟩ := abs_sum_bound
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h0 : 0 ≤ ∑ k ∈ Finset.Icc 1 n, ‖RamanujanPetersson.tau k‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by positivity)]
  exact hK n hn

end RPL2

open UpperHalfPlane Filter Asymptotics MatrixGroups
open scoped Real

open RamanujanPetersson in
theorem solution (s : ℂ) (hs : 13 / 2 < s.re) :
    LSeriesSummable tau s :=
  LSeriesSummable_of_sum_norm_bigO RPL2.tau_sum_isBigO (by norm_num) (by exact_mod_cast hs)
