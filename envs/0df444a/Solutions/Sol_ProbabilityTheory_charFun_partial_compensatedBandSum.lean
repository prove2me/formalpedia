-- Prove2me | solution 1 for ProbabilityTheory.charFun_partial_compensatedBandSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:27:00.639189+00:00
-- url     : https://prove2.me/submissions/5e3892e8-579a-469a-8e85-9e892fdbf3bd

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Theorems.Thm_ProbabilityTheory_charFun_partial_largeJumpSum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal
variable {Ω : Type} [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hf1 : Integrable f (volume.prod ν)) (ξ : ℝ) (n : ℕ) :
    ∫ ω, Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
        compensatedPieceSum K X f (volume.prod ν) k ω) * Complex.I) ∂μ
      = ∏ k ∈ Finset.range (n + 1),
          Complex.exp (∫ x in prmPiece (volume.prod ν) k,
            (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
              ∂(volume.prod ν)) := by
  have hmeasE1 : Measurable fun x : ℝ × ℝ => Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 :=
    (Complex.measurable_exp.comp
      (((Complex.measurable_ofReal.comp hf).const_mul (↑ξ)).mul_const Complex.I)).sub
      measurable_const
  have hboundE1 : ∀ x : ℝ × ℝ, ‖Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1‖ ≤ 2 := fun x => by
    calc ‖Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1‖
        ≤ ‖Complex.exp (↑ξ * ↑(f x) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [show (↑ξ * ↑(f x) * Complex.I : ℂ) = ↑(ξ * f x) * Complex.I from by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  have hE1int : ∀ k, IntegrableOn (fun x : ℝ × ℝ => Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1)
      (prmPiece (volume.prod ν) k) (volume.prod ν) := fun k =>
    IntegrableOn.of_bound measure_prmPiece_lt_top hmeasE1.aestronglyMeasurable 2
      (Filter.Eventually.of_forall hboundE1)
  have hLint : ∀ k, IntegrableOn (fun x : ℝ × ℝ => (↑ξ * ↑(f x) * Complex.I : ℂ))
      (prmPiece (volume.prod ν) k) (volume.prod ν) := by
    intro k
    have h0 : IntegrableOn (fun x : ℝ × ℝ => (↑(f x) : ℂ))
        (prmPiece (volume.prod ν) k) (volume.prod ν) := hf1.integrableOn.ofReal
    exact (h0.const_mul (↑ξ : ℂ)).mul_const Complex.I
  have halg :
      Complex.exp (-(↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
          ∫ x in prmPiece (volume.prod ν) k, f x ∂(volume.prod ν)) * Complex.I))
        * ∏ k ∈ Finset.range (n + 1),
            Complex.exp (∫ x in prmPiece (volume.prod ν) k,
              (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(volume.prod ν))
      = ∏ k ∈ Finset.range (n + 1),
          Complex.exp (∫ x in prmPiece (volume.prod ν) k,
            (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
              ∂(volume.prod ν)) := by
    have hper : ∀ k ∈ Finset.range (n + 1),
        ∫ x in prmPiece (volume.prod ν) k,
            (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
              ∂(volume.prod ν)
          = (∫ x in prmPiece (volume.prod ν) k,
              (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(volume.prod ν))
            - ↑ξ * ↑(∫ x in prmPiece (volume.prod ν) k, f x ∂(volume.prod ν)) * Complex.I := by
      intro k _
      rw [integral_sub (hE1int k) (hLint k)]
      congr 1
      rw [integral_mul_const, integral_const_mul, integral_complex_ofReal]
    simp only [← Complex.exp_sum]
    rw [← Complex.exp_add]
    congr 1
    rw [Finset.sum_congr rfl hper, Finset.sum_sub_distrib]
    have hCeq : (∑ k ∈ Finset.range (n + 1),
          ↑ξ * ↑(∫ x in prmPiece (volume.prod ν) k, f x ∂(volume.prod ν)) * Complex.I)
        = ↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
            ∫ x in prmPiece (volume.prod ν) k, f x ∂(volume.prod ν)) * Complex.I := by
      rw [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
    rw [hCeq]
    ring
  have hexp : ∀ ω, Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
        compensatedPieceSum K X f (volume.prod ν) k ω) * Complex.I)
      = Complex.exp (-(↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
          ∫ x in prmPiece (volume.prod ν) k, f x ∂(volume.prod ν)) * Complex.I))
        * Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
            pieceSum K X f k ω) * Complex.I) := by
    intro ω
    rw [← Complex.exp_add]
    congr 1
    rw [show (∑ k ∈ Finset.range (n + 1), compensatedPieceSum K X f (volume.prod ν) k ω)
          = (∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω)
            - ∑ k ∈ Finset.range (n + 1),
                ∫ x in prmPiece (volume.prod ν) k, f x ∂(volume.prod ν) from by
        rw [← Finset.sum_sub_distrib]; rfl]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp), integral_const_mul,
    charFun_partial_largeJumpSum hd hf ξ n]
  exact halg
