-- Prove2me | solution 1 for SobolevL2.sobolevNorm_natCast_sq_eq_sum_iteratedLineDeriv
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:02:55.900899+00:00
-- url     : https://prove2.me/submissions/fa91f60a-bf09-4102-b3c7-a34cfb3e0f7d

import Mathlib
import Definitions.Def_SobolevL2_SobolevNorm

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform LineDeriv

set_option autoImplicit false

open SobolevL2

namespace Sol_SobolevL2_sobolevNorm_natCast_sq_eq_sum_iteratedLineDeriv

variable {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The `L²` norm of a tempered distribution, `∞` if it is not an `L²` function. -/
noncomputable def nrm [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : 𝓢'(E, F)) : ℝ≥0∞ :=
  ⨅ (g : Lp F 2 (volume : Measure E)) (_ : T = g), ‖g‖ₑ

theorem nrm_eq_of_eq [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : 𝓢'(E, F)) (f : Lp F 2 (volume : Measure E)) (hf : T = f) : nrm T = ‖f‖ₑ := by
  have hinj : ∀ g h : Lp F 2 (volume : Measure E), (g : 𝓢'(E, F)) = h → g = h := by
    intro g h hgh
    exact LinearMap.ker_eq_bot.mp
      (Lp.ker_toTemperedDistributionCLM_eq_bot (F := F) (μ := (volume : Measure E)) (p := 2)) hgh
  unfold nrm
  apply le_antisymm
  · exact iInf₂_le (α := ℝ≥0∞) f hf
  · refine le_iInf₂ fun g hg => ?_
    rw [hinj g f (hg.symm.trans hf)]

theorem nrm_eq_top [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : 𝓢'(E, F)) (h : ¬ ∃ g : Lp F 2 (volume : Measure E), T = g) : nrm T = ⊤ := by
  unfold nrm
  refine le_antisymm le_top (le_iInf₂ fun g hg => ?_)
  exact absurd ⟨g, hg⟩ h

theorem sobolevNorm_eq_nrm [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (s : ℝ) (u : 𝓢'(E, F)) : sobolevNorm s u = nrm (besselPotential E F s u) := rfl

theorem enorm_fourier_Lp [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (f : Lp F 2 (volume : Measure E)) : ‖𝓕 f‖ₑ = ‖f‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
  congr 1
  ext
  exact Lp.norm_fourier_eq f

theorem nrm_fourier [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : 𝓢'(E, F)) : nrm (𝓕 T) = nrm T := by
  by_cases h : ∃ g : Lp F 2 (volume : Measure E), T = g
  · obtain ⟨g, hg⟩ := h
    rw [nrm_eq_of_eq T g hg, nrm_eq_of_eq (𝓕 T) (𝓕 g)
      (by rw [hg, Lp.fourier_toTemperedDistribution_eq g]), enorm_fourier_Lp]
  · rw [nrm_eq_top T h]
    refine nrm_eq_top _ ?_
    rintro ⟨g, hg⟩
    refine h ⟨𝓕⁻ g, ?_⟩
    rw [← Lp.fourierInv_toTemperedDistribution_eq g, ← hg,
      FourierTransform.fourierInv_fourier_eq]

theorem nrm_smul [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (c : ℂ) (hc : c ≠ 0) (T : 𝓢'(E, F)) : nrm (c • T) = ‖c‖ₑ * nrm T := by
  by_cases h : ∃ g : Lp F 2 (volume : Measure E), T = g
  · obtain ⟨g, hg⟩ := h
    rw [nrm_eq_of_eq T g hg, nrm_eq_of_eq (c • T) (c • g), enorm_smul]
    rw [hg, ← Lp.toTemperedDistributionCLM_apply, ← Lp.toTemperedDistributionCLM_apply, map_smul]
  · rw [nrm_eq_top T h, ENNReal.mul_top (by simpa using hc)]
    refine nrm_eq_top _ ?_
    rintro ⟨g, hg⟩
    refine h ⟨c⁻¹ • g, ?_⟩
    rw [← Lp.toTemperedDistributionCLM_apply, map_smul, Lp.toTemperedDistributionCLM_apply, ← hg,
      smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem hasTemperateGrowth_prod_inner {j : ℕ} (m : Fin j → E) :
    (fun x : E ↦ ∏ l, inner ℝ x (m l)).HasTemperateGrowth := by
  have : ∀ s : Finset (Fin j), (fun x : E ↦ ∏ l ∈ s, inner ℝ x (m l)).HasTemperateGrowth := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty]; exact Function.HasTemperateGrowth.const (1 : ℝ)
    | insert a s ha ih =>
      simp_rw [Finset.prod_insert ha]
      exact (Function.hasTemperateGrowth_inner_left (m a)).mul ih
  exact this Finset.univ

open Real in
theorem fourier_iteratedLineDerivOp [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {j : ℕ} (m : Fin j → E) (u : 𝓢'(E, F)) :
    𝓕 (∂^{m} u) = (2 * π * Complex.I) ^ j •
      smulLeftCLM F (fun x : E ↦ ((∏ l, inner ℝ x (m l) : ℝ) : ℂ)) (𝓕 u) := by
  induction j with
  | zero =>
    rw [LineDeriv.iteratedLineDerivOp_fin_zero]
    simp
  | succ j ih =>
    have hP : (fun x : E ↦ ((∏ l, inner ℝ x (Fin.tail m l) : ℝ) : ℂ)).HasTemperateGrowth :=
      by have := hasTemperateGrowth_prod_inner (Fin.tail m); fun_prop
    have hfun : ((fun x : E ↦ ((∏ l, inner ℝ x (Fin.tail m l) : ℝ) : ℂ)) *
        fun x : E ↦ ((inner ℝ x (m 0) : ℝ) : ℂ)) = fun x : E ↦ ((∏ l, inner ℝ x (m l) : ℝ) : ℂ) := by
      funext x
      simp only [Pi.mul_apply, Fin.prod_univ_succ, Complex.ofReal_mul, Fin.tail]
      ring
    rw [LineDeriv.iteratedLineDerivOp_succ_left, fourier_lineDerivOp_eq, ih, map_smul,
      smulLeftCLM_smulLeftCLM_apply hP (by fun_prop), hfun, smul_smul, pow_succ, mul_comm]

theorem sum_sq_prod_inner {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (j : ℕ) (x : E) :
    ∑ i : Fin j → ι, (∏ l, inner ℝ x (b (i l))) ^ 2 = (‖x‖ ^ 2) ^ j := by
  rw [← b.sum_sq_inner_left x, Fintype.sum_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.prod_pow]

theorem real_identity {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ) (x : E) :
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
      ∑ i : Fin j → ι, (∏ l, inner ℝ x (b (i l))) ^ 2 = (1 + ‖x‖ ^ 2) ^ k := by
  simp_rw [sum_sq_prod_inner b]
  rw [add_comm (1 : ℝ), add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [one_pow, mul_one, mul_comm]

theorem rpow_sq_mul_pow (a : ℝ) (ha : 0 < a) (k : ℕ) : (a ^ (-(k : ℝ) / 2)) ^ 2 * a ^ k = 1 := by
  rw [← Real.rpow_natCast (a ^ (-(k : ℝ) / 2)) 2, ← Real.rpow_mul ha.le, ← Real.rpow_natCast a k,
    ← Real.rpow_add ha]
  rw [show -(k : ℝ) / 2 * ((2 : ℕ) : ℝ) + (k : ℝ) = 0 by push_cast; ring, Real.rpow_zero]

theorem rpow_half_mul_rpow_neg_half (a : ℝ) (ha : 0 < a) (k : ℕ) :
    a ^ ((k : ℝ) / 2) * a ^ (-(k : ℝ) / 2) = 1 := by
  rw [← Real.rpow_add ha, show (k : ℝ) / 2 + -(k : ℝ) / 2 = 0 by ring, Real.rpow_zero]

theorem pow_mul_rpow_neg_half (a : ℝ) (ha : 0 < a) (k : ℕ) :
    a ^ k * a ^ (-(k : ℝ) / 2) = a ^ ((k : ℝ) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add ha]
  congr 1
  ring

theorem sq_prod_inner_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {k j : ℕ}
    (hj : j ≤ k) (i : Fin j → ι) (x : E) :
    (∏ l, inner ℝ x (b (i l))) ^ 2 ≤ (1 + ‖x‖ ^ 2) ^ k := by
  rw [← real_identity b k x]
  have h1 : (∏ l, inner ℝ x (b (i l))) ^ 2 ≤ ∑ i' : Fin j → ι, (∏ l, inner ℝ x (b (i' l))) ^ 2 :=
    Finset.single_le_sum (f := fun i' : Fin j → ι ↦ (∏ l, inner ℝ x (b (i' l))) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : ∑ i' : Fin j → ι, (∏ l, inner ℝ x (b (i' l))) ^ 2 ≤
      (k.choose j : ℝ) * ∑ i' : Fin j → ι, (∏ l, inner ℝ x (b (i' l))) ^ 2 := by
    have hc : (1 : ℝ) ≤ (k.choose j : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos hj).ne'
    have hs : 0 ≤ ∑ i' : Fin j → ι, (∏ l, inner ℝ x (b (i' l))) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith
  have h3 : (k.choose j : ℝ) * ∑ i' : Fin j → ι, (∏ l, inner ℝ x (b (i' l))) ^ 2 ≤
      ∑ j' ∈ Finset.range (k + 1), (k.choose j' : ℝ) *
        ∑ i' : Fin j' → ι, (∏ l, inner ℝ x (b (i' l))) ^ 2 :=
    Finset.single_le_sum (f := fun j' ↦ (k.choose j' : ℝ) *
        ∑ i' : Fin j' → ι, (∏ l, inner ℝ x (b (i' l))) ^ 2)
      (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  exact h1.trans (h2.trans h3)

/-- The bounded multiplier `q_i(x) = ∏ₗ ⟪x, b (i l)⟫ · (1 + ‖x‖²)^{-k/2}`. -/
noncomputable def qmul {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ) {j : ℕ}
    (i : Fin j → ι) : E → ℂ :=
  fun x ↦ (((∏ l, inner ℝ x (b (i l))) * (1 + ‖x‖ ^ 2) ^ (-(k : ℝ) / 2) : ℝ) : ℂ)

theorem qmul_hasTemperateGrowth {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ) {j : ℕ}
    (i : Fin j → ι) : (qmul b k i).HasTemperateGrowth := by
  have := hasTemperateGrowth_prod_inner (fun l ↦ b (i l))
  unfold qmul
  fun_prop

theorem norm_qmul_sq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ) {j : ℕ}
    (i : Fin j → ι) (x : E) :
    ‖qmul b k i x‖ ^ 2 = (∏ l, inner ℝ x (b (i l))) ^ 2 * ((1 + ‖x‖ ^ 2) ^ k)⁻¹ := by
  have ha : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  unfold qmul
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
  congr 1
  exact (inv_eq_of_mul_eq_one_left (rpow_sq_mul_pow _ ha k)).symm

theorem norm_qmul_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {k j : ℕ}
    (hj : j ≤ k) (i : Fin j → ι) (x : E) : ‖qmul b k i x‖ ≤ 1 := by
  have ha : (0 : ℝ) < (1 + ‖x‖ ^ 2) ^ k := by positivity
  have h : ‖qmul b k i x‖ ^ 2 ≤ 1 ^ 2 := by
    rw [norm_qmul_sq, one_pow, ← div_eq_mul_inv, div_le_one ha]
    exact sq_prod_inner_le b hj i x
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one two_ne_zero).mp h

theorem qmul_memLp {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {k j : ℕ}
    (hj : j ≤ k) (i : Fin j → ι) : MemLp (qmul b k i) ∞ (volume : Measure E) :=
  memLp_top_of_bound (qmul_hasTemperateGrowth b k i).1.continuous.aestronglyMeasurable 1
    (Eventually.of_forall (norm_qmul_le b hj i))

theorem weight_mul_qmul {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ) {j : ℕ}
    (i : Fin j → ι) :
    (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)) * qmul b k i =
      fun x : E ↦ ((∏ l, inner ℝ x (b (i l)) : ℝ) : ℂ) := by
  funext x
  have ha : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  simp only [Pi.mul_apply, qmul, ← Complex.ofReal_mul]
  congr 1
  rw [mul_left_comm, rpow_half_mul_rpow_neg_half _ ha, mul_one]

theorem sum_enorm_qmul_sq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ) (x : E) :
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ≥0∞) * ∑ i : Fin j → ι, ‖qmul b k i x‖ₑ ^ 2 = 1 := by
  have ha : (0 : ℝ) < (1 + ‖x‖ ^ 2) ^ k := by positivity
  have h : ∀ {j : ℕ} (i : Fin j → ι), ‖qmul b k i x‖ₑ ^ 2 = ENNReal.ofReal (‖qmul b k i x‖ ^ 2) := by
    intro j i
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  simp_rw [h]
  rw [← ENNReal.ofReal_one]
  have hsum : ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * ∑ i : Fin j → ι,
      ‖qmul b k i x‖ ^ 2 = 1 := by
    simp_rw [norm_qmul_sq, ← Finset.sum_mul, ← mul_assoc, ← Finset.sum_mul, real_identity b k x]
    exact mul_inv_cancel₀ ha.ne'
  rw [← hsum, ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]

theorem weight_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ) :
    (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)) =
      fun x : E ↦ ∑ j ∈ Finset.range (k + 1), ∑ i : Fin j → ι,
        ((k.choose j : ℂ) * (((∏ l, inner ℝ x (b (i l)) : ℝ) : ℂ) * qmul b k i x)) := by
  funext x
  have ha : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  simp only [qmul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 1
  rw [← pow_mul_rpow_neg_half _ ha, ← real_identity b k x, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem enorm_sq_Lp [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : Lp F 2 (volume : Measure E)) : ‖f‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp only [one_div, Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    inv_mul_cancel₀, ENNReal.rpow_one, ENNReal.rpow_two]

theorem enorm_sq_smul [NormedAddCommGroup F] [NormedSpace ℂ F] {h : E → ℂ}
    (hh : MemLp h ∞ (volume : Measure E)) (g : Lp F 2 (volume : Measure E)) :
    ‖(hh.toLp h • g : Lp F 2 (volume : Measure E))‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2 * ‖g x‖ₑ ^ 2 := by
  rw [enorm_sq_Lp]
  refine lintegral_congr_ae ?_
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (hh.toLp h) g, hh.coeFn_toLp] with x h1 h2
  rw [h1, Pi.smul_apply', h2, enorm_smul, mul_pow]

theorem smulLeft_prod_eq [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {k j : ℕ} (hj : j ≤ k) (i : Fin j → ι)
    (v : 𝓢'(E, F)) (g : Lp F 2 (volume : Measure E))
    (hg : smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)) v = g) :
    smulLeftCLM F (fun x : E ↦ ((∏ l, inner ℝ x (b (i l)) : ℝ) : ℂ)) v =
      (((qmul_memLp b hj i).toLp (qmul b k i) • g : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
  rw [Lp.toTemperedDistribution_smul_eq (qmul_hasTemperateGrowth b k i) (qmul_memLp b hj i), ← hg,
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (qmul_hasTemperateGrowth b k i),
    weight_mul_qmul]

theorem core_finite [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ)
    (v : 𝓢'(E, F)) (g : Lp F 2 (volume : Measure E))
    (hg : smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)) v = g) :
    ‖g‖ₑ ^ 2 = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ≥0∞) *
      ∑ i : Fin j → ι, nrm (smulLeftCLM F (fun x : E ↦ ((∏ l, inner ℝ x (b (i l)) : ℝ) : ℂ)) v) ^ 2 := by
  have hterm : ∀ j ∈ Finset.range (k + 1), ∀ i : Fin j → ι,
      nrm (smulLeftCLM F (fun x : E ↦ ((∏ l, inner ℝ x (b (i l)) : ℝ) : ℂ)) v) ^ 2 =
        ∫⁻ x, ‖qmul b k i x‖ₑ ^ 2 * ‖g x‖ₑ ^ 2 := by
    intro j hj i
    have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [nrm_eq_of_eq _ _ (smulLeft_prod_eq b hj' i v g hg), enorm_sq_smul]
  have hmeas : ∀ {j : ℕ} (i : Fin j → ι),
      AEMeasurable (fun x ↦ ‖qmul b k i x‖ₑ ^ 2 * ‖g x‖ₑ ^ 2) (volume : Measure E) := by
    intro j i
    exact (((qmul_hasTemperateGrowth b k i).1.continuous.measurable.enorm.pow_const 2).aemeasurable).mul
      ((Lp.aestronglyMeasurable g).enorm.pow_const 2)
  rw [Finset.sum_congr rfl fun j hj => by rw [Finset.sum_congr rfl fun i _ => hterm j hj i],
    enorm_sq_Lp]
  calc ∫⁻ x, ‖g x‖ₑ ^ 2
      = ∫⁻ x, ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ≥0∞) *
          ∑ i : Fin j → ι, ‖qmul b k i x‖ₑ ^ 2 * ‖g x‖ₑ ^ 2 := by
        refine lintegral_congr fun x => ?_
        simp_rw [← Finset.sum_mul, ← mul_assoc, ← Finset.sum_mul, sum_enorm_qmul_sq b k x, one_mul]
    _ = ∑ j ∈ Finset.range (k + 1), ∫⁻ x, (k.choose j : ℝ≥0∞) *
          ∑ i : Fin j → ι, ‖qmul b k i x‖ₑ ^ 2 * ‖g x‖ₑ ^ 2 := by
        refine lintegral_finsetSum' _ fun j _ => ?_
        exact (Finset.aemeasurable_fun_sum _ fun i _ => hmeas i).const_mul _
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _),
          lintegral_finsetSum' _ fun i _ => hmeas i]

theorem smulLeftCLM_fun_sum [NormedAddCommGroup F] [NormedSpace ℂ F] {α : Type*}
    (s : Finset α) (f : α → E → ℂ) (hf : ∀ a ∈ s, (f a).HasTemperateGrowth) (v : 𝓢'(E, F)) :
    smulLeftCLM F (fun x ↦ ∑ a ∈ s, f a x) v = ∑ a ∈ s, smulLeftCLM F (f a) v := by
  rw [smulLeftCLM_sum hf, sum_apply]

theorem exists_of_forall [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ) (v : 𝓢'(E, F))
    (h : ∀ j ≤ k, ∀ i : Fin j → ι, ∃ g : Lp F 2 (volume : Measure E),
      smulLeftCLM F (fun x : E ↦ ((∏ l, inner ℝ x (b (i l)) : ℝ) : ℂ)) v = g) :
    ∃ g : Lp F 2 (volume : Measure E),
      smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)) v = g := by
  classical
  let G : ∀ j : ℕ, (Fin j → ι) → Lp F 2 (volume : Measure E) := fun j i =>
    if hji : ∃ g : Lp F 2 (volume : Measure E),
      smulLeftCLM F (fun x : E ↦ ((∏ l, inner ℝ x (b (i l)) : ℝ) : ℂ)) v = g then hji.choose else 0
  have hG : ∀ j ≤ k, ∀ i : Fin j → ι,
      smulLeftCLM F (fun x : E ↦ ((∏ l, inner ℝ x (b (i l)) : ℝ) : ℂ)) v = G j i := by
    intro j hj i
    simp only [G, dif_pos (h j hj i)]
    exact (h j hj i).choose_spec
  let Q : ∀ j : ℕ, (Fin j → ι) → Lp ℂ ∞ (volume : Measure E) := fun j i =>
    if hj : j ≤ k then (qmul_memLp b hj i).toLp (qmul b k i) else 0
  refine ⟨∑ j ∈ Finset.range (k + 1), ∑ i : Fin j → ι,
    (k.choose j : ℂ) • (Q j i • G j i : Lp F 2 (volume : Measure E)), ?_⟩
  have hPq : ∀ {j : ℕ} (i : Fin j → ι), (fun x : E ↦ (k.choose j : ℂ) *
      (((∏ l, inner ℝ x (b (i l)) : ℝ) : ℂ) * qmul b k i x)).HasTemperateGrowth := by
    intro j i
    have := hasTemperateGrowth_prod_inner (fun l ↦ b (i l))
    have := qmul_hasTemperateGrowth b k i
    fun_prop
  rw [weight_eq_sum b k, smulLeftCLM_fun_sum _ _ (fun j _ => Function.HasTemperateGrowth.sum
      (fun i _ => hPq i)), ← Lp.toTemperedDistributionCLM_apply, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [smulLeftCLM_fun_sum _ _ (fun i _ => hPq i), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hP : (fun x : E ↦ ((∏ l, inner ℝ x (b (i l)) : ℝ) : ℂ)).HasTemperateGrowth := by
    have := hasTemperateGrowth_prod_inner (fun l ↦ b (i l))
    fun_prop
  have hfun : (fun x : E ↦ (k.choose j : ℂ) *
      (((∏ l, inner ℝ x (b (i l)) : ℝ) : ℂ) * qmul b k i x)) =
      (k.choose j : ℂ) • ((fun x : E ↦ ((∏ l, inner ℝ x (b (i l)) : ℝ) : ℂ)) * qmul b k i) := rfl
  rw [hfun, smulLeftCLM_smul (hP.mul (qmul_hasTemperateGrowth b k i)), map_smul,
    ContinuousLinearMap.smul_apply, ← smulLeftCLM_smulLeftCLM_apply hP (qmul_hasTemperateGrowth b k i),
    hG j hj' i, Lp.toTemperedDistributionCLM_apply]
  simp only [Q, dif_pos hj']
  rw [Lp.toTemperedDistribution_smul_eq (qmul_hasTemperateGrowth b k i) (qmul_memLp b hj' i)]

theorem core [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (k : ℕ) (v : 𝓢'(E, F)) :
    nrm (smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)) v) ^ 2 =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ≥0∞) *
        ∑ i : Fin j → ι, nrm (smulLeftCLM F (fun x : E ↦ ((∏ l, inner ℝ x (b (i l)) : ℝ) : ℂ)) v) ^ 2 := by
  by_cases hex : ∃ g : Lp F 2 (volume : Measure E),
      smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)) v = g
  · obtain ⟨g, hg⟩ := hex
    rw [nrm_eq_of_eq _ g hg]
    exact core_finite b k v g hg
  · rw [nrm_eq_top _ hex, ENNReal.top_pow two_ne_zero]
    have hne : ¬ ∀ j ≤ k, ∀ i : Fin j → ι, ∃ g : Lp F 2 (volume : Measure E),
        smulLeftCLM F (fun x : E ↦ ((∏ l, inner ℝ x (b (i l)) : ℝ) : ℂ)) v = g :=
      fun h => hex (exists_of_forall b k v h)
    push_neg at hne
    obtain ⟨j, hj, i, hi⟩ := hne
    symm
    rw [ENNReal.sum_eq_top]
    refine ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj), ?_⟩
    rw [ENNReal.mul_eq_top]
    left
    refine ⟨by exact_mod_cast (Nat.choose_pos hj).ne', ?_⟩
    rw [ENNReal.sum_eq_top]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [nrm_eq_top _ (fun ⟨g, hg⟩ => hi g hg), ENNReal.top_pow two_ne_zero]

end Sol_SobolevL2_sobolevNorm_natCast_sq_eq_sum_iteratedLineDeriv

open Sol_SobolevL2_sobolevNorm_natCast_sq_eq_sum_iteratedLineDeriv in
theorem solution {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (k : ℕ) (u : 𝓢'(E, F)) :
    sobolevNorm (k : ℝ) u ^ 2 =
      ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ≥0∞) * (ENNReal.ofReal (2 * Real.pi) ^ (2 * j))⁻¹ *
          ∑ i : Fin j → ι, sobolevNorm 0 (∂^{fun l => b (i l)} u) ^ 2 := by
  have h2pi : ‖(2 * Real.pi * Complex.I : ℂ)‖ₑ = ENNReal.ofReal (2 * Real.pi) := by
    rw [← ofReal_norm]
    congr 1
    simp [abs_of_pos Real.pi_pos]
  have h2pi_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have ha0 : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hatop : ENNReal.ofReal (2 * Real.pi) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 : sobolevNorm (k : ℝ) u =
      nrm (smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)) (𝓕 u)) := by
    rw [sobolevNorm_eq_nrm, ← nrm_fourier, fourier_besselPotential_eq_smulLeftCLM_fourier_apply]
  have h2 : ∀ {j : ℕ} (i : Fin j → ι), sobolevNorm 0 (∂^{fun l => b (i l)} u) =
      ENNReal.ofReal (2 * Real.pi) ^ j *
        nrm (smulLeftCLM F (fun x : E ↦ ((∏ l, inner ℝ x (b (i l)) : ℝ) : ℂ)) (𝓕 u)) := by
    intro j i
    rw [sobolevNorm_eq_nrm, besselPotential_zero, ContinuousLinearMap.id_apply, ← nrm_fourier,
      fourier_iteratedLineDerivOp, nrm_smul _ (pow_ne_zero _ h2pi_ne), enorm_pow, h2pi]
  rw [h1, core b k (𝓕 u)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [h2, mul_pow, ← pow_mul, ← Finset.mul_sum]
  rw [mul_comm j 2, ← mul_assoc, mul_assoc (k.choose j : ℝ≥0∞),
    ENNReal.inv_mul_cancel (pow_ne_zero _ ha0) (ENNReal.pow_ne_top hatop), mul_one]
