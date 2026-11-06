-- Prove2me | solution 1 for ProbabilityTheory.integral_exp_pieceSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:16:56.490191+00:00
-- url     : https://prove2.me/submissions/76b5ade1-210a-4467-8daf-1fd00c18c68b

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal
variable {Ω : Type} [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}
private lemma toReal_smul_integral_prmPieceLaw_complex {F : Type*} [MeasurableSpace F] [Nonempty F]
    (m : Measure F) [SigmaFinite m] (g : F → ℂ) (k : ℕ) :
    (m (prmPiece m k)).toReal • ∫ x, g x ∂(prmPieceLaw m k)
      = ∫ x in prmPiece m k, g x ∂m := by
  by_cases h : m (prmPiece m k) = 0
  · rw [h, ENNReal.toReal_zero, zero_smul,
      show (∫ x in prmPiece m k, g x ∂m) = ∫ x, g x ∂(m.restrict (prmPiece m k)) from rfl,
      Measure.restrict_eq_zero.mpr h, integral_zero_measure]
  · have hpl : prmPieceLaw m k = (m (prmPiece m k))⁻¹ • m.restrict (prmPiece m k) := by
      unfold prmPieceLaw; rw [if_neg h]
    rw [hpl, integral_smul_measure, smul_smul, ENNReal.toReal_inv,
      mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨h, measure_prmPiece_lt_top.ne⟩), one_smul]

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) (ξ : ℝ)
    (k : ℕ) :
    ∫ ω, Complex.exp (↑ξ * ↑(pieceSum K X f k ω) * Complex.I) ∂μ
      = Complex.exp (∫ x in prmPiece (volume.prod ν) k,
          (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(volume.prod ν)) := by
  have hwmeas : Measurable fun x : ℝ × ℝ => Complex.exp (↑ξ * ↑(f x) * Complex.I) :=
    Complex.measurable_exp.comp
      (((Complex.measurable_ofReal.comp hf).const_mul (↑ξ)).mul_const Complex.I)
  have hwbdd : ∀ x : ℝ × ℝ, ‖Complex.exp (↑ξ * ↑(f x) * Complex.I)‖ ≤ 1 := fun x => by
    rw [show (↑ξ * ↑(f x) * Complex.I : ℂ) = ↑(ξ * f x) * Complex.I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hw_int : Integrable (fun x : ℝ × ℝ => Complex.exp (↑ξ * ↑(f x) * Complex.I))
      (prmPieceLaw (volume.prod ν) k) :=
    Integrable.of_bound hwmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall hwbdd)
  have hprod : ∀ ω, ∏ n ∈ Finset.range (K k ω),
        Complex.exp (↑ξ * ↑(f (X k n ω)) * Complex.I)
      = Complex.exp (↑ξ * ↑(pieceSum K X f k ω) * Complex.I) := by
    intro ω
    rw [← Complex.exp_sum]
    congr 1
    simp only [pieceSum, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  have hone : ∫ _x : ℝ × ℝ, (1 : ℂ) ∂(prmPieceLaw (volume.prod ν) k) = 1 := by
    simp
  have hint : ∫ ω, Complex.exp (↑ξ * ↑(pieceSum K X f k ω) * Complex.I) ∂μ
      = ∫ ω, ∏ n ∈ Finset.range (K k ω), Complex.exp (↑ξ * ↑(f (X k n ω)) * Complex.I) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => (hprod ω).symm)
  rw [hint, integral_pieceProd_eq_exp hd hwmeas hwbdd]
  congr 1
  rw [show (∫ x, Complex.exp (↑ξ * ↑(f x) * Complex.I) ∂(prmPieceLaw (volume.prod ν) k)) - 1
        = ∫ x, (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(prmPieceLaw (volume.prod ν) k) from by
      rw [integral_sub hw_int (integrable_const 1), hone],
    ← Complex.real_smul]
  exact toReal_smul_integral_prmPieceLaw_complex _ _ k
