-- Prove2me | solution 1 for SymPolyOpt.Putinar.only_if_computation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:43:49.13222+00:00
-- url     : https://prove2.me/submissions/27d073ef-3eb4-497b-9ad2-8d50ce65310a

import Mathlib
import Definitions.Def_SymPolyOpt_Putinar_Setting

open MeasureTheory MvPolynomial

open SymPolyOpt.Putinar in
theorem solution {n m : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [Fintype G]
    (g : Fin m → MvPolynomial (Fin n) ℝ) (hg : ∀ j, IsGInvariant G (g j))
    (hK : IsCompact (feasK g)) (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ]
    (hμK : μ (feasK g)ᶜ = 0) (hμG : IsGInvariantMeasure G μ)
    (j : Fin (m + 1)) (f : MvPolynomial (Fin n) ℝ) :
    ∫ x, eval x ((1 / (Fintype.card G : ℝ)) •
          ∑ σ : G, polyAct (σ : GL (Fin n) ℝ) (f * f) * gExt g j) ∂μ =
        ∫ x, eval x (f * f * gExt g j) ∂μ ∧
      0 ≤ ∫ x, eval x (f * f * gExt g j) ∂μ := by
  -- evaluation of the action
  have hev : ∀ (σ : GL (Fin n) ℝ) (x : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ),
      eval x (polyAct σ p) = eval (ptAct σ⁻¹ x) p := by
    intro σ x p
    unfold polyAct ptAct
    show aeval x (aeval _ p) = aeval _ p
    rw [comp_aeval_apply]
    congr 1
    congr 1
    funext i
    simp [map_sum, Matrix.mulVec, dotProduct]
  -- invariance of gExt
  have hpolyMul : ∀ (σ : GL (Fin n) ℝ) (p q : MvPolynomial (Fin n) ℝ),
      polyAct σ (p * q) = polyAct σ p * polyAct σ q := by
    intro σ p q; unfold polyAct; exact map_mul _ _ _
  have hgExt : ∀ σ ∈ G, polyAct σ (gExt g j) = gExt g j := by
    intro σ hσ
    refine Fin.cases ?_ (fun i => ?_) j
    · show polyAct σ 1 = 1
      unfold polyAct; exact map_one _
    · show polyAct σ (g i) = g i
      exact hg i σ hσ
  -- integrability of polynomials
  have hae : ∀ᵐ x ∂μ, x ∈ feasK g := mem_ae_iff.mpr hμK
  have hrestrict : μ.restrict (feasK g) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have hint : ∀ p : MvPolynomial (Fin n) ℝ, Integrable (fun x => eval x p) μ := by
    intro p
    have hc : Continuous (fun x : Fin n → ℝ => eval x p) := MvPolynomial.continuous_eval p
    have := hc.continuousOn.integrableOn_compact (μ := μ) hK
    rw [IntegrableOn, hrestrict] at this
    exact this
  have hmeasP : ∀ σ : GL (Fin n) ℝ, Measurable (ptAct σ) := by
    intro σ
    unfold ptAct
    exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  -- each summand integrates to the same value
  have hsummand : ∀ σ : G, ∫ x, eval x (polyAct (σ : GL (Fin n) ℝ) (f * f) * gExt g j) ∂μ =
      ∫ x, eval x (f * f * gExt g j) ∂μ := by
    intro σ
    have e : polyAct (σ : GL (Fin n) ℝ) (f * f) * gExt g j =
        polyAct (σ : GL (Fin n) ℝ) (f * f * gExt g j) := by
      rw [hpolyMul (σ : GL (Fin n) ℝ) (f * f) (gExt g j), hgExt σ σ.2]
    rw [e]
    simp_rw [hev]
    have hinv : (σ : GL (Fin n) ℝ)⁻¹ ∈ G := G.inv_mem σ.2
    have hmap := hμG _ hinv
    rw [← integral_map (hmeasP _).aemeasurable
      (MvPolynomial.continuous_eval _).aestronglyMeasurable, hmap]
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  constructor
  · simp only [smul_eval, map_sum]
    rw [integral_const_mul, integral_finset_sum _ (fun σ _ => hint _)]
    simp_rw [hsummand]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · apply integral_nonneg_of_ae
    filter_upwards [hae] with x hx
    have hgx : 0 ≤ eval x (gExt g j) := by
      refine Fin.cases ?_ (fun i => ?_) j
      · show 0 ≤ eval x (1 : MvPolynomial (Fin n) ℝ)
        simp
      · show 0 ≤ eval x (g i)
        exact hx i
    simp only [map_mul, Pi.zero_apply]
    exact mul_nonneg (mul_self_nonneg _) hgx
