-- Prove2me | solution 1 for RamanujanPetersson.L_functional_equation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:59:34.118859+00:00
-- url     : https://prove2.me/submissions/760c5996-1d29-4aeb-84bb-b0bb4bc7b1bb

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

lemma Lsumm (s : ℂ) (hs : 13 / 2 < s.re) : LSeriesSummable RamanujanPetersson.tau s :=
  LSeriesSummable_of_sum_norm_bigO tau_sum_isBigO (by norm_num) (by exact_mod_cast hs)

end RPL2

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups Complex Filter
open scoped Real

namespace RPFE

noncomputable abbrev D : CuspForm 𝒮ℒ 12 := CuspForm.discriminant

lemma hk : (0 : ℤ) < 12 := by norm_num

noncomputable def LL (s : ℂ) : ℂ := ModularForm.L hk D s

lemma LL_diff : Differentiable ℂ LL := CuspForm.differentiable_L hk D

lemma LL_eq_seven (s : ℂ) (hs : 7 < s.re) :
    LL s = LSeries RamanujanPetersson.tau s := by
  unfold RamanujanPetersson.tau
  have h := CuspForm.hasSum_L (Γ := 𝒮ℒ) hk D (s := s) (by norm_num; linarith)
  rw [Subgroup.strictWidthInfty_SL2Z] at h
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul] at h
  rw [LSeries, LL]
  refine (HasSum.tsum_eq ?_).symm
  convert h using 1
  funext n
  rw [LSeries.term_def]
  split_ifs with hn
  · subst hn
    have : s ≠ 0 := by rintro rfl; simp at hs; linarith
    simp [Complex.zero_cpow this]
  · rfl

lemma translate_eq : (⇑(translate D ModularGroup.S) : ℍ → ℂ) = ⇑D := by
  rw [coe_translate]
  exact SlashInvariantFormClass.slash_action_eq D _ ⟨ModularGroup.S, rfl⟩

lemma Λ_symm : (weakFEPair hk D).symm.Λ = (weakFEPair hk D).Λ := by
  rw [(CuspForm.isStrongFEPair hk D).symm.Λ_eq, (CuspForm.isStrongFEPair hk D).Λ_eq]
  congr 1
  funext t
  simp only [WeakFEPair.symm, weakFEPair_g, weakFEPair_f]
  rw [translate_eq]

lemma Λ_fe (s : ℂ) : Λ hk D (12 - s) = Λ hk D s := by
  have h := (weakFEPair hk D).functional_equation s
  rw [Λ_symm] at h
  simp only [weakFEPair_k, weakFEPair_ε] at h
  have hI : (Complex.I) ^ (12 : ℤ) = 1 := by
    rw [show (12 : ℤ) = ((12 : ℕ) : ℤ) from rfl, zpow_natCast, show 12 = 2 * 6 from rfl, pow_mul,
      Complex.I_sq]; norm_num
  rw [hI, one_smul] at h
  simpa [Λ] using h

lemma gamma_L (s : ℂ) (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) :
    Complex.Gamma s * LL s / (2 * (π : ℂ)) ^ s = Λ hk D s := by
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have hp : (2 * (π : ℂ)) ^ s ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]; left; exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  rw [LL, ModularForm.L, Complex.Gammaℂ_def, Complex.cpow_neg]
  field_simp

end RPFE

open UpperHalfPlane Filter Asymptotics MatrixGroups
open scoped Real

open RamanujanPetersson in
theorem solution :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      (∀ s : ℂ, 13 / 2 < s.re → L s = LSeries tau s) ∧
      ∀ s : ℂ, (∀ n : ℕ, s ≠ -(n : ℂ)) → (∀ n : ℕ, 12 - s ≠ -(n : ℂ)) →
        Complex.Gamma s * L s / (2 * (π : ℂ)) ^ s =
          Complex.Gamma (12 - s) * L (12 - s) / (2 * (π : ℂ)) ^ (12 - s) := by
  refine ⟨RPFE.LL, RPFE.LL_diff, ?_, ?_⟩
  · have habs : LSeries.abscissaOfAbsConv tau ≤ ((13 / 2 : ℝ) : EReal) :=
      LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
        RPL2.Lsumm y (by simpa using hy)
    have hU : AnalyticOnNhd ℂ (LSeries tau) {s : ℂ | 13 / 2 < s.re} :=
      (LSeries_analyticOnNhd tau).mono fun s hs =>
        lt_of_le_of_lt habs (by exact_mod_cast (show (13 / 2 : ℝ) < s.re from hs))
    have hL : AnalyticOnNhd ℂ RPFE.LL {s : ℂ | 13 / 2 < s.re} :=
      fun s _ => RPFE.LL_diff.analyticAt s
    have heq := hL.eqOn_of_preconnected_of_eventuallyEq hU
      (convex_halfSpace_re_gt (13 / 2 : ℝ)).isPreconnected (z₀ := 8)
      (by show (13 / 2 : ℝ) < (8 : ℂ).re; norm_num) ?_
    · exact fun s hs => heq hs
    · filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (7 : ℝ) < (8 : ℂ).re by norm_num)] with s hs
      exact RPFE.LL_eq_seven s hs
  · intro s h1 h2
    rw [RPFE.gamma_L s h1, RPFE.gamma_L _ h2, RPFE.Λ_fe]
