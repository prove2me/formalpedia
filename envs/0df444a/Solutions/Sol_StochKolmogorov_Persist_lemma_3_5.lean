-- Prove2me | solution 1 for StochKolmogorov.Persist.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T23:15:42.68701+00:00
-- url     : https://prove2.me/submissions/b6085f7a-6e61-4f02-91c4-762732e69211

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

namespace L35_8bddb3e6

theorem sq_mul_exp_le (θ₀ θ y : ℝ) (hθ₀ : 0 < θ₀) (h0 : 0 ≤ θ) (h1 : θ ≤ θ₀ / 2) :
    y ^ 2 * Real.exp (θ * y) ≤ 8 / θ₀ ^ 2 * (Real.exp (θ₀ * y) + Real.exp (-θ₀ * y)) := by
  set a := θ₀ * |y| / 2 with ha
  have ha0 : 0 ≤ a := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg ha0
  have hy2 : y ^ 2 ≤ 8 / θ₀ ^ 2 * Real.exp a := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have e : a ^ 2 = θ₀ ^ 2 * y ^ 2 / 4 := by rw [ha, div_pow, mul_pow, sq_abs]; ring
    nlinarith
  have hexp : Real.exp (θ * y) ≤ Real.exp a := by
    apply Real.exp_le_exp.2
    have h2 : θ * y ≤ θ * |y| := mul_le_mul_of_nonneg_left (le_abs_self y) h0
    have h3 : θ * |y| ≤ θ₀ / 2 * |y| := mul_le_mul_of_nonneg_right h1 (abs_nonneg y)
    have h4 : a = θ₀ / 2 * |y| := by rw [ha]; ring
    linarith
  have habs : Real.exp (θ₀ * |y|) ≤ Real.exp (θ₀ * y) + Real.exp (-θ₀ * y) := by
    rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; linarith [Real.exp_pos (-θ₀ * y)]
    · rw [h]
      have : θ₀ * -y = -θ₀ * y := by ring
      rw [this]; linarith [Real.exp_pos (θ₀ * y)]
  calc y ^ 2 * Real.exp (θ * y) ≤ (8 / θ₀ ^ 2 * Real.exp a) * Real.exp a :=
        mul_le_mul hy2 hexp (Real.exp_pos _).le (by positivity)
    _ = 8 / θ₀ ^ 2 * Real.exp (θ₀ * |y|) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; rw [ha]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left habs (by positivity)

theorem exp_neg_le (θ₀ θ y : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ θ₀) :
    Real.exp (-θ * y) ≤ 1 + Real.exp (-θ₀ * y) := by
  rcases le_total 0 y with hy | hy
  · have : Real.exp (-θ * y) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    linarith [Real.exp_pos (-θ₀ * y)]
  · have : Real.exp (-θ * y) ≤ Real.exp (-θ₀ * y) := Real.exp_le_exp.2 (by nlinarith)
    linarith

theorem amgm_exp (m θ y : ℝ) (hm : 0 < m) :
    (2 : ℝ) ≤ m * Real.exp (θ * y) + Real.exp (-θ * y) / m := by
  have he : Real.exp (-θ * y) = (Real.exp (θ * y))⁻¹ := by rw [neg_mul, Real.exp_neg]
  rw [he]
  have he0 := Real.exp_pos (θ * y)
  set e := Real.exp (θ * y)
  rw [← sub_nonneg]
  have : m * e + e⁻¹ / m - 2 = (m * e - 1) ^ 2 / (m * e) := by
    field_simp; ring
  rw [this]; positivity

theorem main (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (K₁ : ℝ) :
    ∃ K₂ : ℝ, 0 < K₂ ∧ ∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (Y : Ω' → ℝ),
      Integrable (fun ω => Real.exp (θ₀ * Y ω)) P' →
      Integrable (fun ω => Real.exp (-θ₀ * Y ω)) P' →
      ∫ ω, Real.exp (θ₀ * Y ω) ∂P' + ∫ ω, Real.exp (-θ₀ * Y ω) ∂P' ≤ K₁ →
        (∀ θ ∈ Set.Ico 0 (θ₀ / 2), DifferentiableAt ℝ (cgf Y P') θ ∧
          DifferentiableAt ℝ (deriv (cgf Y P')) θ) ∧
        deriv (cgf Y P') 0 = ∫ ω, Y ω ∂P' ∧
        ∀ θ ∈ Set.Ico 0 (θ₀ / 2),
          0 ≤ iteratedDeriv 2 (cgf Y P') θ ∧ iteratedDeriv 2 (cgf Y P') θ ≤ K₂ := by
  refine ⟨8 * |K₁| * (1 + |K₁|) / θ₀ ^ 2 + 1, by positivity, ?_⟩
  intro Ω' _ P' _ Y hp hm hK
  have hsub : Set.Ioo (-θ₀) θ₀ ⊆ integrableExpSet Y P' := fun t ht =>
    integrable_exp_mul_of_le_of_le hm hp ht.1.le ht.2.le
  have hint : ∀ θ ∈ Set.Ioo (-θ₀) θ₀, θ ∈ interior (integrableExpSet Y P') := fun θ hθ =>
    interior_maximal hsub isOpen_Ioo hθ
  have hIco : ∀ θ ∈ Set.Ico 0 (θ₀ / 2), θ ∈ interior (integrableExpSet Y P') := fun θ hθ =>
    hint θ ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hK1 : 0 ≤ K₁ := le_trans (add_nonneg (integral_nonneg fun _ => (Real.exp_pos _).le)
    (integral_nonneg fun _ => (Real.exp_pos _).le)) hK
  refine ⟨fun θ hθ => ⟨(analyticAt_cgf (hIco θ hθ)).differentiableAt,
    (analyticAt_cgf (hIco θ hθ)).deriv.differentiableAt⟩, ?_, fun θ hθ => ⟨?_, ?_⟩⟩
  · rw [deriv_cgf_zero (hint 0 ⟨by linarith, hθ₀⟩)]
    simp
  · rw [iteratedDeriv_two_cgf_eq_integral (hIco θ hθ)]
    exact div_nonneg (integral_nonneg fun ω => by positivity) mgf_nonneg
  · have hθi := hIco θ hθ
    have hposi : Integrable (fun ω => Real.exp (θ * Y ω)) P' := interior_subset (s := integrableExpSet Y P') hθi
    have hmp : 0 < mgf Y P' θ := mgf_pos hposi
    have hnegi : Integrable (fun ω => Real.exp (-θ * Y ω)) P' :=
      interior_subset (s := integrableExpSet Y P') (hint (-θ) ⟨by linarith [hθ.2], by linarith [hθ.1]⟩)
    have hmn : 0 < mgf Y P' (-θ) := mgf_pos hnegi
    have ep : ∫ ω, Real.exp (θ * Y ω) ∂P' = mgf Y P' θ := rfl
    have en : ∫ ω, Real.exp (-θ * Y ω) ∂P' = mgf Y P' (-θ) := rfl
    have hmnle : mgf Y P' (-θ) ≤ 1 + K₁ := by
      have h1 : ∫ ω, Real.exp (-θ * Y ω) ∂P' ≤ ∫ ω, (1 + Real.exp (-θ₀ * Y ω)) ∂P' :=
        integral_mono hnegi ((integrable_const 1).add hm) fun ω =>
          exp_neg_le θ₀ θ (Y ω) hθ.1 (by linarith [hθ.2])
      rw [integral_add (integrable_const 1) hm, en] at h1
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
      have : 0 ≤ ∫ ω, Real.exp (θ₀ * Y ω) ∂P' := integral_nonneg fun ω => (Real.exp_pos (θ₀ * Y ω)).le
      linarith
    have hprod : 1 ≤ mgf Y P' θ * mgf Y P' (-θ) := by
      have h2 : ∫ _ω, (2 : ℝ) ∂P' ≤ ∫ ω, (mgf Y P' (-θ) * Real.exp (θ * Y ω) +
          Real.exp (-θ * Y ω) / mgf Y P' (-θ)) ∂P' :=
        integral_mono (integrable_const 2) ((hposi.const_mul _).add (hnegi.div_const _))
          fun ω => amgm_exp _ θ (Y ω) hmn
      rw [integral_add (hposi.const_mul _) (hnegi.div_const _), integral_const_mul,
        integral_div, ep, en, div_self hmn.ne'] at h2
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h2
      nlinarith
    have hnum : ∫ ω, Y ω ^ 2 * Real.exp (θ * Y ω) ∂P' ≤ 8 / θ₀ ^ 2 * K₁ := by
      calc _ ≤ ∫ ω, 8 / θ₀ ^ 2 * (Real.exp (θ₀ * Y ω) + Real.exp (-θ₀ * Y ω)) ∂P' :=
            integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity) ((hp.add hm).const_mul _)
              (ae_of_all _ fun ω => sq_mul_exp_le θ₀ θ (Y ω) hθ₀ hθ.1 hθ.2.le)
        _ = 8 / θ₀ ^ 2 * (∫ ω, Real.exp (θ₀ * Y ω) ∂P' + ∫ ω, Real.exp (-θ₀ * Y ω) ∂P') := by
            rw [integral_const_mul, integral_add hp hm]
        _ ≤ 8 / θ₀ ^ 2 * K₁ := mul_le_mul_of_nonneg_left hK (by positivity)
    have h3 : 1 ≤ (1 + K₁) * mgf Y P' θ := by nlinarith
    have hA : 0 ≤ 8 / θ₀ ^ 2 * K₁ := by positivity
    have hdiv : (∫ ω, Y ω ^ 2 * Real.exp (θ * Y ω) ∂P') / mgf Y P' θ ≤
        8 / θ₀ ^ 2 * K₁ * (1 + K₁) := by
      rw [div_le_iff₀ hmp]
      calc _ ≤ 8 / θ₀ ^ 2 * K₁ := hnum
        _ = 8 / θ₀ ^ 2 * K₁ * 1 := (mul_one _).symm
        _ ≤ 8 / θ₀ ^ 2 * K₁ * ((1 + K₁) * mgf Y P' θ) := mul_le_mul_of_nonneg_left h3 hA
        _ = _ := by ring
    have hK2 : 8 / θ₀ ^ 2 * K₁ * (1 + K₁) ≤ 8 * |K₁| * (1 + |K₁|) / θ₀ ^ 2 + 1 := by
      rw [abs_of_nonneg hK1]
      have : 8 / θ₀ ^ 2 * K₁ * (1 + K₁) = 8 * K₁ * (1 + K₁) / θ₀ ^ 2 := by ring
      linarith
    rw [iteratedDeriv_two_cgf hθi]
    linarith [sq_nonneg (deriv (cgf Y P') θ)]

end L35_8bddb3e6

open MeasureTheory ProbabilityTheory Filter in
theorem solution (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (K₁ : ℝ) :
    ∃ K₂ : ℝ, 0 < K₂ ∧ ∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (Y : Ω' → ℝ),
      Integrable (fun ω => Real.exp (θ₀ * Y ω)) P' →
      Integrable (fun ω => Real.exp (-θ₀ * Y ω)) P' →
      ∫ ω, Real.exp (θ₀ * Y ω) ∂P' + ∫ ω, Real.exp (-θ₀ * Y ω) ∂P' ≤ K₁ →
        (∀ θ ∈ Set.Ico 0 (θ₀ / 2), DifferentiableAt ℝ (cgf Y P') θ ∧
          DifferentiableAt ℝ (deriv (cgf Y P')) θ) ∧
        deriv (cgf Y P') 0 = ∫ ω, Y ω ∂P' ∧
        ∀ θ ∈ Set.Ico 0 (θ₀ / 2),
          0 ≤ iteratedDeriv 2 (cgf Y P') θ ∧ iteratedDeriv 2 (cgf Y P') θ ≤ K₂ := by
  exact L35_8bddb3e6.main θ₀ hθ₀ K₁
