-- Prove2me | solution 1 for ScenarioExact.PartOne.moment_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:43:11.533999+00:00
-- url     : https://prove2.me/submissions/52968834-1d33-4c65-8953-d5fb6778210b

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
import Definitions.Def_ScenarioApproach_Generalization_supportConstraint
import Definitions.Def_ScenarioExact_PartOne_Basic
open MeasureTheory ScenarioApproach.Generalization
open scoped ENNReal


namespace ScenarioExact.PartOne

theorem se_bin_deriv (N : ℕ) : ∀ d : ℕ, d ≤ N → ∀ α : ℝ,
    HasDerivAt (fun x : ℝ => ∑ i ∈ Finset.range d, (N.choose i : ℝ) * x ^ i * (1 - x) ^ (N - i))
      (-((N.choose d : ℝ) * d * α ^ (d - 1) * (1 - α) ^ (N - d))) α := by
  intro d
  induction d with
  | zero => intro _ α; simpa using hasDerivAt_const α (0 : ℝ)
  | succ d ih =>
    intro hd α
    obtain ⟨k, hk⟩ : ∃ k, N - d = k + 1 := ⟨N - d - 1, by omega⟩
    have hk2 : N - (d + 1) = k := by omega
    have hC : ((N.choose (d + 1) : ℕ) : ℝ) * ((d : ℝ) + 1) = (N.choose d : ℝ) * ((k : ℝ) + 1) := by
      have := Nat.choose_succ_right_eq N d
      rw [hk] at this
      exact_mod_cast this
    have h1 := ih (by omega) α
    have h2 : HasDerivAt (fun x : ℝ => (N.choose d : ℝ) * x ^ d * (1 - x) ^ (N - d))
        ((N.choose d : ℝ) * ((d : ℝ) * α ^ (d - 1)) * (1 - α) ^ (N - d) +
          (N.choose d : ℝ) * α ^ d * (((N - d : ℕ) : ℝ) * (1 - α) ^ (N - d - 1) * (-1))) α := by
      have ha := (hasDerivAt_pow d α).const_mul (N.choose d : ℝ)
      have hb := ((hasDerivAt_id α).const_sub 1).pow (N - d)
      exact ha.mul hb
    have h3 := h1.add h2
    simp_rw [Finset.sum_range_succ]
    refine h3.congr_deriv ?_
    rw [hk, hk2]
    simp only [Nat.add_sub_cancel]
    push_cast
    linear_combination (α ^ d * (1 - α) ^ k) * hC

theorem se_bin_identity {d N : ℕ} (hd : 1 ≤ d) (hN : d ≤ N) (ε : ℝ) :
    (N.choose d : ℝ) * ∫ α in ε..1, (1 - α) ^ (N - d) * ((d : ℝ) * α ^ (d - 1)) =
      ∑ i ∈ Finset.range d, (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i) := by
  rw [← intervalIntegral.integral_const_mul]
  have hder : ∀ x ∈ Set.uIcc ε 1, HasDerivAt
      (fun x : ℝ => -∑ i ∈ Finset.range d, (N.choose i : ℝ) * x ^ i * (1 - x) ^ (N - i))
      ((N.choose d : ℝ) * ((1 - x) ^ (N - d) * ((d : ℝ) * x ^ (d - 1)))) x := by
    intro x _
    exact (se_bin_deriv N d hN x).neg.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (by
    apply Continuous.intervalIntegrable; fun_prop)]
  have h1 : ∑ i ∈ Finset.range d, (N.choose i : ℝ) * (1:ℝ) ^ i * (1 - 1) ^ (N - i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have : N - i ≠ 0 := by have := Finset.mem_range.mp hi; omega
    simp [zero_pow this]
  simp only [h1]
  ring

theorem se_lint_Icc (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) (hf : Continuous f)
    (hnn : ∀ x ∈ Set.Icc a b, 0 ≤ f x) :
    ∫⁻ x in Set.Icc a b, ENNReal.ofReal (f x) = ENNReal.ofReal (∫ x in a..b, f x) := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal (hf.integrableOn_Icc)
      (ae_restrict_of_forall_mem measurableSet_Icc hnn)]

theorem se_exist {d : ℕ} (hd : 1 ≤ d) : ∀ m : ℕ, d ≤ m →
      (m.choose d : ℝ≥0∞) *
          ∫⁻ α in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - α) ^ (m - d) * ((d : ℝ) * α ^ (d - 1))) =
        1 := by
  intro m hm
  rw [se_lint_Icc 0 1 zero_le_one _ (by fun_prop) (fun x hx => by
    have := hx.1; have := hx.2; positivity)]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), se_bin_identity hd hm]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi; simp [zero_pow hi]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

theorem se_poly_ext (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0) (hν : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ k : ℕ, ∫ x in Set.Icc (0 : ℝ) 1, (1 - x) ^ k ∂μ = ∫ x in Set.Icc (0 : ℝ) 1, (1 - x) ^ k ∂ν) :
    μ = ν := by
  have hμr : μ.restrict (Set.Icc 0 1) = μ := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; exact hμ)
  have hνr : ν.restrict (Set.Icc 0 1) = ν := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]; exact hν)
  have hpoly : ∀ p : Polynomial ℝ, ∫ x in Set.Icc (0 : ℝ) 1, p.eval x ∂μ =
      ∫ x in Set.Icc (0 : ℝ) 1, p.eval x ∂ν := by
    intro p
    set q := p.comp (1 - Polynomial.X) with hq
    have hpq : ∀ x, p.eval x = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (1 - x) ^ i := by
      intro x
      rw [← Polynomial.eval_eq_sum_range, hq, Polynomial.eval_comp]
      simp
    simp_rw [hpq]
    rw [integral_finsetSum _ (fun i _ => (by fun_prop : Continuous fun x : ℝ =>
      q.coeff i * (1 - x) ^ i).integrableOn_Icc),
      integral_finsetSum _ (fun i _ => (by fun_prop : Continuous fun x : ℝ =>
      q.coeff i * (1 - x) ^ i).integrableOn_Icc)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_const_mul, hmom i]
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have e1 : ∫ x, f x ∂μ = ∫ x in Set.Icc (0:ℝ) 1, f x ∂μ := by rw [hμr]
  have e2 : ∫ x, f x ∂ν = ∫ x in Set.Icc (0:ℝ) 1, f x ∂ν := by rw [hνr]
  rw [e1, e2]
  apply eq_of_forall_dist_le
  intro ε hε
  set A := μ.real (Set.Icc (0:ℝ) 1) + ν.real (Set.Icc (0:ℝ) 1) + 1 with hA
  have hApos : 0 < A := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 (fun x => f x)
    f.continuous.continuousOn (ε / A) (by positivity)
  have hfi : ∀ m : Measure ℝ, [IsFiniteMeasure m] →
      IntegrableOn (fun x => f x) (Set.Icc (0:ℝ) 1) m := fun m _ => (f.integrable _)
  have hpi : ∀ m : Measure ℝ, [IsFiniteMeasure m] →
      IntegrableOn (fun x => p.eval x) (Set.Icc (0:ℝ) 1) m :=
    fun m _ => (Polynomial.continuous p).integrableOn_Icc
  have hb : ∀ m : Measure ℝ, [IsFiniteMeasure m] →
      ‖∫ x in Set.Icc (0:ℝ) 1, (f x - p.eval x) ∂m‖ ≤ ε / A * m.real (Set.Icc (0:ℝ) 1) := by
    intro m _
    apply norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
    intro x hx
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact (hp x hx).le
  have hμb := hb μ
  have hνb := hb ν
  rw [integral_sub (hfi μ) (hpi μ)] at hμb
  rw [integral_sub (hfi ν) (hpi ν)] at hνb
  rw [Real.dist_eq]
  have hpo := hpoly p
  have h1 : |(∫ x in Set.Icc (0:ℝ) 1, f x ∂μ) - ∫ x in Set.Icc (0:ℝ) 1, f x ∂ν| ≤
      ε / A * μ.real (Set.Icc (0:ℝ) 1) + ε / A * ν.real (Set.Icc (0:ℝ) 1) := by
    rw [Real.norm_eq_abs] at hμb hνb
    calc _ = |((∫ x in Set.Icc (0:ℝ) 1, f x ∂μ) - ∫ x in Set.Icc (0:ℝ) 1, p.eval x ∂μ) -
          ((∫ x in Set.Icc (0:ℝ) 1, f x ∂ν) - ∫ x in Set.Icc (0:ℝ) 1, p.eval x ∂ν)| := by
            rw [hpo]; ring_nf
      _ ≤ _ := (abs_sub _ _).trans (add_le_add hμb hνb)
  refine h1.trans ?_
  have : ε / A * μ.real (Set.Icc (0:ℝ) 1) + ε / A * ν.real (Set.Icc (0:ℝ) 1) =
      ε * ((μ.real (Set.Icc (0:ℝ) 1) + ν.real (Set.Icc (0:ℝ) 1)) / A) := by ring
  rw [this]
  have hle : (μ.real (Set.Icc (0:ℝ) 1) + ν.real (Set.Icc (0:ℝ) 1)) / A ≤ 1 := by
    rw [div_le_one hApos]; linarith
  nlinarith [measureReal_nonneg (μ := μ) (s := Set.Icc (0:ℝ) 1),
    measureReal_nonneg (μ := ν) (s := Set.Icc (0:ℝ) 1)]

/-- the law with density `d α^{d-1}` on `[0,1]` -/
noncomputable def seDens (d : ℕ) : Measure ℝ :=
  (volume.restrict (Set.Icc (0:ℝ) 1)).withDensity (fun x => ENNReal.ofReal ((d : ℝ) * x ^ (d - 1)))

theorem seDens_Iic {d : ℕ} (hd : 1 ≤ d) (α : ℝ) (hα : α ∈ Set.Icc (0:ℝ) 1) :
    seDens d (Set.Iic α) = ENNReal.ofReal (α ^ d) := by
  rw [seDens, withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have : Set.Iic α ∩ Set.Icc (0:ℝ) 1 = Set.Icc 0 α := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hα.2⟩
  rw [this, se_lint_Icc 0 α hα.1 _ (by fun_prop) (fun x hx => by have := hx.1; positivity)]
  congr 1
  rw [intervalIntegral.integral_const_mul, integral_pow]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  simp

theorem seDens_compl (d : ℕ) : seDens d (Set.Icc (0:ℝ) 1)ᶜ = 0 := by
  rw [seDens, withDensity_apply _ measurableSet_Icc.compl,
    Measure.restrict_restrict measurableSet_Icc.compl, Set.compl_inter_self, Measure.restrict_empty,
    lintegral_zero_measure]

instance seDens_finite (d : ℕ) : IsFiniteMeasure (seDens d) := by
  refine ⟨?_⟩
  rw [seDens, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    se_lint_Icc 0 1 zero_le_one _ (by fun_prop) (fun x hx => by have := hx.1; positivity)]
  exact ENNReal.ofReal_lt_top

theorem seDens_mom (d k : ℕ) :
    ∫⁻ x in Set.Icc (0:ℝ) 1, ENNReal.ofReal ((1 - x) ^ k) ∂(seDens d) =
      ∫⁻ x in Set.Icc (0:ℝ) 1, ENNReal.ofReal ((1 - x) ^ k * ((d : ℝ) * x ^ (d - 1))) := by
  rw [seDens, setLIntegral_withDensity_eq_setLIntegral_mul _ (by fun_prop) (by fun_prop)
    measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc, Set.inter_self]
  refine setLIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
  have h1 : 0 ≤ 1 - x := by linarith [hx.2]
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (by have := hx.1; positivity), mul_comm]

theorem mu_core {d : ℕ} (hd : 1 ≤ d) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ m : ℕ, d ≤ m →
        (m.choose d : ℝ≥0∞) * ∫⁻ α in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - α) ^ (m - d)) ∂μ = 1) :
    ∀ α ∈ Set.Icc (0 : ℝ) 1, μ (Set.Iic α) = ENNReal.ofReal (α ^ d) := by
  have hlin : ∀ k : ℕ, ∫⁻ α in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - α) ^ k) ∂μ =
      ∫⁻ α in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - α) ^ k) ∂(seDens d) := by
    intro k
    have h1 := hmom (d + k) (by omega)
    have h2 := se_exist hd (d + k) (by omega)
    rw [Nat.add_sub_cancel_left] at h1 h2
    rw [← seDens_mom] at h2
    have hC0 : ((d + k).choose d : ℝ≥0∞) ≠ 0 := by
      have := Nat.choose_pos (show d ≤ d + k by omega); exact_mod_cast this.ne'
    exact (ENNReal.mul_right_inj hC0 (ENNReal.natCast_ne_top _)).mp (h1.trans h2.symm)
  have hreal : ∀ k : ℕ, ∫ x in Set.Icc (0 : ℝ) 1, (1 - x) ^ k ∂μ =
      ∫ x in Set.Icc (0 : ℝ) 1, (1 - x) ^ k ∂(seDens d) := by
    intro k
    have hnn : ∀ m : Measure ℝ, 0 ≤ᵐ[m.restrict (Set.Icc (0:ℝ) 1)] fun x : ℝ => (1 - x) ^ k :=
      fun m => ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => by
        have : 0 ≤ 1 - x := by linarith [hx.2]
        positivity)
    rw [integral_eq_lintegral_of_nonneg_ae (hnn μ) (by fun_prop),
      integral_eq_lintegral_of_nonneg_ae (hnn _) (by fun_prop), hlin k]
  have heq := se_poly_ext μ (seDens d) hμ (seDens_compl d) hreal
  intro α hα
  rw [heq, seDens_Iic hd α hα]

theorem moment_core {d : ℕ} (hd : 1 ≤ d) :
    (∀ m : ℕ, d ≤ m →
      (m.choose d : ℝ≥0∞) *
          ∫⁻ α in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - α) ^ (m - d) * ((d : ℝ) * α ^ (d - 1))) =
        1) ∧
    ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
      (∀ m : ℕ, d ≤ m →
        (m.choose d : ℝ≥0∞) * ∫⁻ α in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - α) ^ (m - d)) ∂μ = 1) →
      ∀ α ∈ Set.Icc (0 : ℝ) 1, μ (Set.Iic α) = ENNReal.ofReal (α ^ d) :=
  ⟨se_exist hd, fun μ _ hμ hmom => mu_core hd μ hμ hmom⟩

end ScenarioExact.PartOne

open ScenarioExact.PartOne


theorem solution {d : ℕ} (hd : 1 ≤ d) :
    -- existence: the law with density `d α^{d-1}` on `[0, 1]` (distribution function `α^d`) solves (3.4)
    (∀ m : ℕ, d ≤ m →
      (m.choose d : ℝ≥0∞) *
          ∫⁻ α in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - α) ^ (m - d) * ((d : ℝ) * α ^ (d - 1))) =
        1) ∧
    -- uniqueness: every probability law on `[0, 1]` solving (3.4) has distribution function `α^d`
    ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
      (∀ m : ℕ, d ≤ m →
        (m.choose d : ℝ≥0∞) * ∫⁻ α in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - α) ^ (m - d)) ∂μ = 1) →
      ∀ α ∈ Set.Icc (0 : ℝ) 1, μ (Set.Iic α) = ENNReal.ofReal (α ^ d) := by
  exact moment_core hd
