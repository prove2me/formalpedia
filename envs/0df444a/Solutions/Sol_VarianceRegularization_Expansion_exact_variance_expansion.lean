-- Prove2me | solution 1 for VarianceRegularization.Expansion.exact_variance_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T17:37:27.902972+00:00
-- url     : https://prove2.me/submissions/f61ef6cf-1be9-4cca-933f-fe0c97d2f285

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_robustSup
import Definitions.Def_VarianceRegularization_Expansion_empVar

set_option autoImplicit false

open MeasureTheory

namespace VarianceRegularization.Expansion.EVE3d62

open VarianceRegularization.Expansion ProbabilityTheory

lemma sum_dev {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) :
    ∑ i, (z i - empMean z) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, empMean]
  field_simp
  ring

lemma sum_sq_dev {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) :
    ∑ i, (z i - empMean z) ^ 2 = n * empVar z := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hm : ∑ i, z i = n * empMean z := by
    simp only [empMean]; field_simp
  have h : ∀ i, (z i - empMean z) ^ 2 = z i ^ 2 - 2 * empMean z * z i + empMean z ^ 2 :=
    fun i => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hm, empVar]
  field_simp
  ring

lemma sum_dev_mul {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) :
    ∑ i, (z i - empMean z) * z i = n * empVar z := by
  have h : ∀ i, (z i - empMean z) * z i = (z i - empMean z) ^ 2 + empMean z * (z i - empMean z) :=
    fun i => by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, sum_dev hn, sum_sq_dev hn]
  ring

lemma mean_mem {n : ℕ} (hn : 0 < n) (M₀ M₁ : ℝ) (z : Fin n → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc M₀ M₁) :
    M₀ ≤ empMean z ∧ empMean z ≤ M₁ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℝ) * M₀ ≤ ∑ i, z i := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hz i).1)
    simpa using this
  have h2 : ∑ i, z i ≤ (n : ℝ) * M₁ := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hz i).2)
    simpa using this
  unfold empMean
  constructor
  · rw [le_inv_mul_iff₀ hnpos]; linarith
  · rw [inv_mul_le_iff₀ hnpos]; linarith

theorem suff_main {n : ℕ} (hn : 0 < n) (ρ M₀ M₁ : ℝ)
    (hρ : 0 ≤ ρ) (hM : M₀ ≤ M₁) (z : Fin n → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc M₀ M₁)
    (hvar : 0 < empVar z)
    (h30 : 2 * ρ * (M₁ - M₀) ^ 2 / (n : ℝ) ≤ empVar z) :
    robustSup n ρ z = empMean z + Real.sqrt (2 * ρ / (n : ℝ) * empVar z) := by
  have hsd := sum_dev hn z
  have hssd := sum_sq_dev hn z
  have hsdm := sum_dev_mul hn z
  obtain ⟨hm0, hm1⟩ := mean_mem hn M₀ M₁ z hz
  set m := empMean z with hm_def
  set V := empVar z with hV_def
  set S := Real.sqrt (2 * ρ / (n : ℝ) * V) with hS_def
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = 2 * ρ / n * V := Real.sq_sqrt (by positivity)
  unfold robustSup
  apply IsGreatest.csSup_eq
  constructor
  · -- attainment
    set c := S / (n * V) with hc
    have hc0 : 0 ≤ c := by positivity
    have hSM : S * (M₁ - M₀) ≤ V := by
      have hsq : (S * (M₁ - M₀)) ^ 2 ≤ V ^ 2 := by
        have e : (S * (M₁ - M₀)) ^ 2 = 2 * ρ * (M₁ - M₀) ^ 2 / n * V := by
          rw [mul_pow, hS2]; ring
        rw [e]
        calc 2 * ρ * (M₁ - M₀) ^ 2 / n * V ≤ V * V := mul_le_mul_of_nonneg_right h30 hvar.le
          _ = V ^ 2 := (sq V).symm
      have h0 : 0 ≤ S * (M₁ - M₀) := mul_nonneg hS0 (by linarith)
      nlinarith
    have hcM : c * (M₁ - M₀) ≤ 1 / n := by
      rw [hc, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hnpos]
      nlinarith
    refine ⟨fun i => 1 / n + c * (z i - m), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro i
      have hzi := hz i
      have hd : -(z i - m) ≤ M₁ - M₀ := by linarith [hzi.1]
      have := mul_le_mul_of_nonneg_left hd hc0
      show 0 ≤ 1 / (n : ℝ) + c * (z i - m)
      nlinarith
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsd, mul_zero, add_zero, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · have h : ∀ i, ((n : ℝ) * (1 / n + c * (z i - m)) - 1) ^ 2 = (n * c) ^ 2 * (z i - m) ^ 2 := by
        intro i; field_simp; ring
      simp only [h, ← Finset.mul_sum, hssd]
      have key : (n * c) ^ 2 * (n * V) = 2 * ρ := by
        rw [hc]
        have hV0 : V ≠ 0 := hvar.ne'
        have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
        field_simp
        rw [hS2]
        field_simp
      rw [key]; linarith
    · show ∑ i, (1 / (n : ℝ) + c * (z i - m)) * z i = m + S
      have h : ∀ i, (1 / (n : ℝ) + c * (z i - m)) * z i = (1 / n) * z i + c * ((z i - m) * z i) :=
        fun i => by ring
      simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, hsdm]
      rw [hc, hm_def]
      simp only [empMean]
      field_simp
  · -- upper bound
    rintro _ ⟨p, ⟨hp0, hp1, hpc⟩, rfl⟩
    show ∑ i, p i * z i ≤ m + S
    have hid : ∑ i, p i * z i - m = ∑ i, (p i - 1 / n) * (z i - m) := by
      have h : ∀ i, (p i - 1 / n) * (z i - m) = p i * z i - m * p i - (1 / n) * (z i - m) :=
        fun i => by ring
      simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, hsd, hp1]
      ring
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => p i - 1 / n) (fun i => z i - m)
    have hp2 : ∑ i, (p i - 1 / (n : ℝ)) ^ 2 = (1 / (n : ℝ) ^ 2) * ∑ i, ((n : ℝ) * p i - 1) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
      field_simp
    have hx2 : (∑ i, p i * z i - m) ^ 2 ≤ 2 * ρ / n * V := by
      rw [hid]
      refine hcs.trans ?_
      rw [hp2, hssd]
      have hb : ∑ i, ((n : ℝ) * p i - 1) ^ 2 ≤ 2 * ρ := by linarith
      have : (1 / (n : ℝ) ^ 2 * ∑ i, ((n : ℝ) * p i - 1) ^ 2) * (n * V) ≤
          1 / (n : ℝ) ^ 2 * (2 * ρ) * (n * V) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hb (by positivity)
      refine this.trans (le_of_eq ?_)
      field_simp
    have := Real.abs_le_sqrt hx2
    have := le_abs_self (∑ i, p i * z i - m)
    linarith


lemma empVar_eq {n : ℕ} (hn : 0 < n) (μ0 : ℝ) (z : Fin n → ℝ) :
    empVar z = (n : ℝ)⁻¹ * ∑ i, (z i - μ0) ^ 2 - ((n : ℝ)⁻¹ * ∑ i, (z i - μ0)) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h : ∀ i, (z i - μ0) ^ 2 = z i ^ 2 - 2 * μ0 * z i + μ0 ^ 2 := fun i => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, empVar, empMean]
  field_simp
  ring

lemma numeric (a : ℝ) (ha : 44 ≤ a) :
    Real.exp (-(49 / 400) * a) + 2 * Real.exp (-(28 / 55) * a) ≤ Real.exp (-a / 11) := by
  have e1 : Real.exp (-(49 / 400) * a) = Real.exp (-a / 11) * Real.exp (-((139 / 4400) * a)) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(28 / 55) * a) = Real.exp (-a / 11) * Real.exp (-((23 / 55) * a)) := by
    rw [← Real.exp_add]; ring_nf
  have b1 : Real.exp (-((139 / 4400) * a)) ≤ 1 / 2 := by
    have h1 := Real.add_one_le_exp ((139 / 4400) * a)
    have h2 : Real.exp (-((139 / 4400) * a)) * Real.exp ((139 / 4400) * a) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos (-((139 / 4400) * a))
    nlinarith
  have b2 : Real.exp (-((23 / 55) * a)) ≤ 1 / 4 := by
    have h1 := Real.add_one_le_exp ((23 / 55) * a)
    have h2 : Real.exp (-((23 / 55) * a)) * Real.exp ((23 / 55) * a) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos (-((23 / 55) * a))
    nlinarith
  have h0 := Real.exp_pos (-a / 11)
  rw [e1, e2]
  nlinarith

lemma hoeff_tail {n : ℕ} (P : Measure ℝ) [IsProbabilityMeasure P] {M₀ M₁ : ℝ}
    (hae : ∀ᵐ x ∂P, x ∈ Set.Icc M₀ M₁) (ε : ℝ) (hε : 0 ≤ ε) (sg : ℝ) (hsg : sg = 1 ∨ sg = -1) :
    (Measure.pi (fun _ : Fin n => P)).real {z | ε ≤ ∑ i, sg * (z i - ∫ x, x ∂P)} ≤
      Real.exp (-ε ^ 2 / (2 * (n * ((M₁ - M₀) / 2) ^ 2))) := by
  set μ0 := ∫ x, x ∂P with hμ0def
  set μn := Measure.pi (fun _ : Fin n => P) with hμn
  have hsub : ∀ i : Fin n, HasSubgaussianMGF (fun z : Fin n → ℝ => sg * (z i - μ0))
      ((‖M₁ - M₀‖₊ / 2) ^ 2) μn := by
    intro i
    have hae' : ∀ᵐ z ∂μn, z i ∈ Set.Icc M₀ M₁ :=
      (measurePreserving_eval (fun _ : Fin n => P) i).quasiMeasurePreserving.ae hae
    have h := hasSubgaussianMGF_of_mem_Icc (X := fun z : Fin n → ℝ => z i) (μ := μn)
      (measurable_pi_apply i).aemeasurable hae'
    have hmean : (∫ z, z i ∂μn) = μ0 := integral_eval
    rw [hmean] at h
    rcases hsg with rfl | rfl
    · convert h using 1
      funext z; ring
    · convert h.neg using 1
      funext z; simp
  have hind : iIndepFun (fun i (z : Fin n → ℝ) => sg * (z i - μ0)) μn :=
    iIndepFun_pi (X := fun _ x => sg * (x - μ0)) (fun _ => by fun_prop)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind (c := fun _ => (‖M₁ - M₀‖₊ / 2) ^ 2)
    (s := Finset.univ) (fun i _ => hsub i) hε
  refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
  · rfl
  · congr 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [Real.norm_eq_abs, div_pow, sq_abs, div_pow]

lemma lower_tail {n : ℕ} (P : Measure ℝ) [IsProbabilityMeasure P] {M₀ M₁ : ℝ}
    (hMpos : 0 < M₁ - M₀)
    (hae : ∀ᵐ x ∂P, x ∈ Set.Icc M₀ M₁) (hμ0 : (∫ x, x ∂P) ∈ Set.Icc M₀ M₁) :
    (Measure.pi (fun _ : Fin n => P)).real
      {z | ∑ i, (z i - ∫ x, x ∂P) ^ 2 ≤ n * (3 / 10 * ∫ x, (x - ∫ y, y ∂P) ^ 2 ∂P)} ≤
    Real.exp (-(49 / 400) * (n * (∫ x, (x - ∫ y, y ∂P) ^ 2 ∂P) / (M₁ - M₀) ^ 2)) := by
  set μ0 := ∫ x, x ∂P with hμ0def
  set σ2 := ∫ x, (x - μ0) ^ 2 ∂P with hσ2def
  set μn := Measure.pi (fun _ : Fin n => P) with hμn
  set M := M₁ - M₀ with hMdef
  set t : ℝ := -(7 / 20) / M ^ 2 with ht
  have hM2 : 0 < M ^ 2 := by positivity
  have ht0 : t ≤ 0 := by
    rw [ht]; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hM2.le
  have htM : t * M ^ 2 = -(7 / 20) := by rw [ht]; field_simp
  have hY : ∀ᵐ x ∂P, (x - μ0) ^ 2 ∈ Set.Icc 0 (M ^ 2) := by
    filter_upwards [hae] with x hx
    refine ⟨sq_nonneg _, ?_⟩
    have h1 : x - μ0 ≤ M := by rw [hMdef]; linarith [hx.2, hμ0.1]
    have h2 : -M ≤ x - μ0 := by rw [hMdef]; linarith [hx.1, hμ0.2]
    exact sq_le_sq' h2 h1
  have hpt : ∀ᵐ x ∂P, Real.exp (t * (x - μ0) ^ 2) ≤ 1 + (t + t ^ 2 * M ^ 2) * (x - μ0) ^ 2 := by
    filter_upwards [hY] with x hx
    set y := (x - μ0) ^ 2
    have hty : t * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ht0 hx.1
    have hty2 : -(7 / 20) ≤ t * y := by
      have := mul_nonneg_of_nonpos_of_nonpos ht0 (sub_nonpos.mpr hx.2)
      nlinarith
    have hu : |t * y| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have hb' := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hu)).2
    have hyy : y * y ≤ M ^ 2 * y := mul_le_mul_of_nonneg_right hx.2 hx.1
    have hy2 : (t * y) ^ 2 ≤ t ^ 2 * M ^ 2 * y := by
      have := mul_le_mul_of_nonneg_left hyy (sq_nonneg t)
      nlinarith
    nlinarith
  have hYint : Integrable (fun x => (x - μ0) ^ 2) P :=
    Integrable.of_mem_Icc 0 (M ^ 2) (by fun_prop) hY
  have hEint : Integrable (fun x => Real.exp (t * (x - μ0) ^ 2)) P := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg ht0 (sq_nonneg _)
  have hone : ∫ x, Real.exp (t * (x - μ0) ^ 2) ∂P ≤ Real.exp ((t + t ^ 2 * M ^ 2) * σ2) := by
    calc ∫ x, Real.exp (t * (x - μ0) ^ 2) ∂P
        ≤ ∫ x, (1 + (t + t ^ 2 * M ^ 2) * (x - μ0) ^ 2) ∂P :=
          integral_mono_ae hEint ((integrable_const 1).add (hYint.const_mul _)) hpt
      _ = 1 + (t + t ^ 2 * M ^ 2) * σ2 := by
          rw [integral_add (integrable_const 1) (hYint.const_mul _), integral_const,
            integral_const_mul]
          simp [hσ2def]
      _ ≤ Real.exp ((t + t ^ 2 * M ^ 2) * σ2) := by
          linarith [Real.add_one_le_exp ((t + t ^ 2 * M ^ 2) * σ2)]
  let Y : Fin n → (Fin n → ℝ) → ℝ := fun i z => (z i - μ0) ^ 2
  have hind : iIndepFun Y μn := iIndepFun_pi (X := fun _ x => (x - μ0) ^ 2) (fun _ => by fun_prop)
  have hmeas : ∀ i, Measurable (Y i) := fun i => by
    show Measurable (fun z : Fin n → ℝ => (z i - μ0) ^ 2)
    fun_prop
  have hmgf : ∀ i, mgf (Y i) μn t = ∫ x, Real.exp (t * (x - μ0) ^ 2) ∂P := by
    intro i
    simp only [mgf, Y]
    exact integral_comp_eval (μ := fun _ => P) (f := fun x => Real.exp (t * (x - μ0) ^ 2))
      (by fun_prop)
  have hsm : Measurable (∑ i, Y i) := by
    have h := Finset.measurable_fun_sum (f := Y) Finset.univ (fun i _ => hmeas i)
    convert h using 1
    ext z
    simp [Finset.sum_apply]
  have hint : Integrable (fun z => Real.exp (t * (∑ i, Y i) z)) μn := by
    refine Integrable.of_bound ((Real.measurable_exp.comp (hsm.const_mul t)).aestronglyMeasurable)
      1 (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    apply mul_nonpos_of_nonpos_of_nonneg ht0
    rw [Finset.sum_apply]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hch := measure_le_le_exp_mul_mgf (μ := μn) (X := ∑ i, Y i) (n * (3 / 10 * σ2)) ht0 hint
  rw [hind.mgf_sum hmeas] at hch
  have hset : {z : Fin n → ℝ | ∑ i, (z i - μ0) ^ 2 ≤ n * (3 / 10 * σ2)} =
      {z | (∑ i, Y i) z ≤ n * (3 / 10 * σ2)} := by
    ext z; simp [Y, Finset.sum_apply]
  rw [hset]
  refine hch.trans ?_
  have hprod : ∏ i ∈ Finset.univ, mgf (Y i) μn t ≤ Real.exp ((t + t ^ 2 * M ^ 2) * σ2) ^ n := by
    calc ∏ i ∈ Finset.univ, mgf (Y i) μn t
        ≤ ∏ i ∈ (Finset.univ : Finset (Fin n)), Real.exp ((t + t ^ 2 * M ^ 2) * σ2) :=
          Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => (hmgf i).le.trans hone)
      _ = _ := by simp
  calc Real.exp (-t * (n * (3 / 10 * σ2))) * ∏ i ∈ Finset.univ, mgf (Y i) μn t
      ≤ Real.exp (-t * (n * (3 / 10 * σ2))) * Real.exp ((t + t ^ 2 * M ^ 2) * σ2) ^ n :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (-t * (n * (3 / 10 * σ2)) + n * ((t + t ^ 2 * M ^ 2) * σ2)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ = _ := by
        congr 1; rw [ht]; field_simp; ring

set_option maxHeartbeats 1000000 in
theorem eve_main {n : ℕ} (hn : 0 < n) (ρ M₀ M₁ : ℝ)
    (hρ : 0 ≤ ρ) (hM : M₀ ≤ M₁) (P : Measure ℝ)
    [IsProbabilityMeasure P] (hsupp : P (Set.Icc M₀ M₁) = 1)
    (hvar : 0 < ProbabilityTheory.variance (id : ℝ → ℝ) P)
    (hsize : max 5 (((M₁ - M₀) ^ 2 /
        ProbabilityTheory.variance (id : ℝ → ℝ) P) *
        max (8 * Real.sqrt (ProbabilityTheory.variance (id : ℝ → ℝ) P))
          (max 44 (44 * ρ))) ≤ (n : ℝ)) :
    (Measure.pi (fun _ : Fin n => P))
        {z : Fin n → ℝ |
          robustSup n ρ z ≠
            empMean z + Real.sqrt (2 * ρ / (n : ℝ) * empVar z)} ≤
      ENNReal.ofReal (Real.exp
        (-(n : ℝ) * ProbabilityTheory.variance (id : ℝ → ℝ) P /
          (11 * (M₁ - M₀) ^ 2))) := by
  classical
  set σ2 := ProbabilityTheory.variance (id : ℝ → ℝ) P with hσ2
  set μn := Measure.pi (fun _ : Fin n => P) with hμn
  rcases eq_or_lt_of_le (sub_nonneg.mpr hM) with hM0 | hMpos
  · have h0 : (M₁ - M₀) ^ 2 = 0 := by rw [← hM0]; ring
    rw [h0, mul_zero, div_zero, Real.exp_zero, ENNReal.ofReal_one]
    exact prob_le_one
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hae : ∀ᵐ x ∂P, x ∈ Set.Icc M₀ M₁ :=
    mem_ae_iff.mpr ((prob_compl_eq_zero_iff measurableSet_Icc).mpr hsupp)
  set μ0 := ∫ x, x ∂P with hμ0def
  have hidint : Integrable (fun x : ℝ => x) P := Integrable.of_mem_Icc M₀ M₁ aemeasurable_id hae
  have hμ0 : μ0 ∈ Set.Icc M₀ M₁ := by
    constructor
    · have := integral_mono_ae (integrable_const M₀) hidint (hae.mono fun x hx => hx.1)
      simpa using this
    · have := integral_mono_ae hidint (integrable_const M₁) (hae.mono fun x hx => hx.2)
      simpa using this
  have hσ2eq : σ2 = ∫ x, (x - μ0) ^ 2 ∂P := by
    rw [hσ2, variance_eq_integral aemeasurable_id]
    simp only [id]
    rw [← hμ0def]
  have hM2 : 0 < (M₁ - M₀) ^ 2 := by positivity
  have hA : (M₁ - M₀) ^ 2 / σ2 * 44 ≤ n :=
    le_trans (mul_le_mul_of_nonneg_left (le_trans (le_max_left _ _) (le_max_right _ _))
      (by positivity)) (le_trans (le_max_right _ _) hsize)
  have hB : (M₁ - M₀) ^ 2 / σ2 * (44 * ρ) ≤ n :=
    le_trans (mul_le_mul_of_nonneg_left (le_trans (le_max_right _ _) (le_max_right _ _))
      (by positivity)) (le_trans (le_max_right _ _) hsize)
  have ha : 44 ≤ n * σ2 / (M₁ - M₀) ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hvar] at hA
    rw [le_div_iff₀ hM2]; linarith
  have hρ' : 2 * ρ * (M₁ - M₀) ^ 2 / n ≤ σ2 / 22 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hvar] at hB
    rw [div_le_iff₀ hnpos]; nlinarith
  set s := Real.sqrt (14 / 55 * σ2) with hsdef
  have hs2 : s ^ 2 = 14 / 55 * σ2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsub : {z : Fin n → ℝ | robustSup n ρ z ≠
        empMean z + Real.sqrt (2 * ρ / (n : ℝ) * empVar z)} ⊆
      {z : Fin n → ℝ | ¬ ∀ i, z i ∈ Set.Icc M₀ M₁} ∪
        {z | ∑ i, (z i - μ0) ^ 2 ≤ n * (3 / 10 * σ2)} ∪
        {z | n * s ≤ ∑ i, (1 : ℝ) * (z i - μ0)} ∪
        {z | n * s ≤ ∑ i, (-1 : ℝ) * (z i - μ0)} := by
    intro z hz
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_le] at hcon
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hcon
    apply hz
    simp only [one_mul] at h2
    simp only [neg_one_mul, Finset.sum_neg_distrib] at h3
    have hD2 : (∑ i, (z i - μ0)) ^ 2 < (n * s) ^ 2 := sq_lt_sq' (by linarith) h2
    have hev : σ2 / 22 ≤ empVar z := by
      rw [empVar_eq hn μ0 z]
      have e1 : 3 / 10 * σ2 < (n : ℝ)⁻¹ * ∑ i, (z i - μ0) ^ 2 := by
        rw [lt_inv_mul_iff₀ hnpos]; linarith
      have e2 : ((n : ℝ)⁻¹ * ∑ i, (z i - μ0)) ^ 2 < 14 / 55 * σ2 := by
        rw [mul_pow, inv_pow, inv_mul_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    exact suff_main hn ρ M₀ M₁ hρ hM z h0 (by linarith) (le_trans hρ' hev)
  have hA0 : μn {z : Fin n → ℝ | ¬ ∀ i, z i ∈ Set.Icc M₀ M₁} = 0 := by
    rw [← ae_iff]
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin n => P) i).quasiMeasurePreserving.ae hae
  have hL := lower_tail (n := n) P hMpos hae hμ0
  have hH1 := hoeff_tail (n := n) P hae (n * s) (by positivity) 1 (Or.inl rfl)
  have hH2 := hoeff_tail (n := n) P hae (n * s) (by positivity) (-1) (Or.inr rfl)
  rw [← hμ0def, ← hσ2eq, ← hμn] at hL
  rw [← hμ0def, ← hμn] at hH1 hH2
  have hexp : -(n * s) ^ 2 / (2 * (n * ((M₁ - M₀) / 2) ^ 2)) =
      -(28 / 55) * (n * σ2 / (M₁ - M₀) ^ 2) := by
    rw [mul_pow, hs2]; field_simp; ring
  rw [hexp] at hH1 hH2
  have hnum := numeric _ ha
  have hfin : -(n : ℝ) * σ2 / (11 * (M₁ - M₀) ^ 2) = -(n * σ2 / (M₁ - M₀) ^ 2) / 11 := by
    rw [show (11 * (M₁ - M₀) ^ 2) = (M₁ - M₀) ^ 2 * 11 by ring, ← div_div, neg_mul, neg_div]
  rw [hfin]
  calc μn {z : Fin n → ℝ | robustSup n ρ z ≠
        empMean z + Real.sqrt (2 * ρ / (n : ℝ) * empVar z)}
      ≤ μn ({z : Fin n → ℝ | ¬ ∀ i, z i ∈ Set.Icc M₀ M₁} ∪
        {z | ∑ i, (z i - μ0) ^ 2 ≤ n * (3 / 10 * σ2)} ∪
        {z | n * s ≤ ∑ i, (1 : ℝ) * (z i - μ0)} ∪
        {z | n * s ≤ ∑ i, (-1 : ℝ) * (z i - μ0)}) := measure_mono hsub
    _ ≤ μn {z : Fin n → ℝ | ¬ ∀ i, z i ∈ Set.Icc M₀ M₁} +
        μn {z | ∑ i, (z i - μ0) ^ 2 ≤ n * (3 / 10 * σ2)} +
        μn {z | n * s ≤ ∑ i, (1 : ℝ) * (z i - μ0)} +
        μn {z | n * s ≤ ∑ i, (-1 : ℝ) * (z i - μ0)} :=
      by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ = ENNReal.ofReal (μn.real {z | ∑ i, (z i - μ0) ^ 2 ≤ n * (3 / 10 * σ2)}) +
        ENNReal.ofReal (μn.real {z | n * s ≤ ∑ i, (1 : ℝ) * (z i - μ0)}) +
        ENNReal.ofReal (μn.real {z | n * s ≤ ∑ i, (-1 : ℝ) * (z i - μ0)}) := by
      rw [hA0, zero_add, ofReal_measureReal, ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-(49 / 400) * (n * σ2 / (M₁ - M₀) ^ 2))) +
        ENNReal.ofReal (Real.exp (-(28 / 55) * (n * σ2 / (M₁ - M₀) ^ 2))) +
        ENNReal.ofReal (Real.exp (-(28 / 55) * (n * σ2 / (M₁ - M₀) ^ 2))) := by
      gcongr
    _ = ENNReal.ofReal (Real.exp (-(49 / 400) * (n * σ2 / (M₁ - M₀) ^ 2)) +
        2 * Real.exp (-(28 / 55) * (n * σ2 / (M₁ - M₀) ^ 2))) := by
      rw [two_mul, ← add_assoc, ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (Real.exp (-(n * σ2 / (M₁ - M₀) ^ 2) / 11)) :=
      ENNReal.ofReal_le_ofReal hnum

end VarianceRegularization.Expansion.EVE3d62

open MeasureTheory VarianceRegularization.Expansion in
theorem solution {n : ℕ} (hn : 0 < n) (ρ M₀ M₁ : ℝ)
    (hρ : 0 ≤ ρ) (hM : M₀ ≤ M₁) (P : Measure ℝ)
    [IsProbabilityMeasure P] (hsupp : P (Set.Icc M₀ M₁) = 1)
    (hvar : 0 < ProbabilityTheory.variance (id : ℝ → ℝ) P)
    (hsize : max 5 (((M₁ - M₀) ^ 2 /
        ProbabilityTheory.variance (id : ℝ → ℝ) P) *
        max (8 * Real.sqrt (ProbabilityTheory.variance (id : ℝ → ℝ) P))
          (max 44 (44 * ρ))) ≤ (n : ℝ)) :
    (Measure.pi (fun _ : Fin n => P))
        {z : Fin n → ℝ |
          robustSup n ρ z ≠
            empMean z + Real.sqrt (2 * ρ / (n : ℝ) * empVar z)} ≤
      ENNReal.ofReal (Real.exp
        (-(n : ℝ) * ProbabilityTheory.variance (id : ℝ → ℝ) P /
          (11 * (M₁ - M₀) ^ 2))) := by
  exact VarianceRegularization.Expansion.EVE3d62.eve_main hn ρ M₀ M₁ hρ hM P hsupp hvar hsize
