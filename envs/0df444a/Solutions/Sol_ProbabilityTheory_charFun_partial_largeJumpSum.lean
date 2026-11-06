-- Prove2me | solution 1 for ProbabilityTheory.charFun_partial_largeJumpSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:21:13.859348+00:00
-- url     : https://prove2.me/submissions/b75acd61-41a7-41e1-8623-6f2567bc2150

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Theorems.Thm_ProbabilityTheory_integral_exp_pieceSum
import Theorems.Thm_ProbabilityTheory_indepFun_partialPieceSum_pieceSum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal
variable {Ω : Type} [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) (ξ : ℝ)
    (n : ℕ) :
    ∫ ω, Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω) * Complex.I) ∂μ
      = ∏ k ∈ Finset.range (n + 1),
          Complex.exp (∫ x in prmPiece (volume.prod ν) k,
            (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(volume.prod ν)) := by
  have hgmeas : Measurable fun r : ℝ => Complex.exp (↑ξ * ↑r * Complex.I) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.const_mul (↑ξ)).mul_const Complex.I)
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, Finset.prod_range_one]
    exact integral_exp_pieceSum hd hf ξ 0
  | succ n ih =>
    have hexp : ∀ ω,
        Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 2), pieceSum K X f k ω) * Complex.I)
          = Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω) * Complex.I)
            * Complex.exp (↑ξ * ↑(pieceSum K X f (n + 1) ω) * Complex.I) := by
      intro ω
      rw [← Complex.exp_add]
      congr 1
      rw [Finset.sum_range_succ]
      push_cast
      ring
    have hmL : Measurable fun ω =>
        Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω) * Complex.I) :=
      hgmeas.comp (Finset.measurable_sum _ fun k _ =>
        measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hf)
    have hmR : Measurable fun ω =>
        Complex.exp (↑ξ * ↑(pieceSum K X f (n + 1) ω) * Complex.I) :=
      hgmeas.comp (measurable_pieceSum (hd.measurable_count _) (hd.measurable_point _) hf)
    have hind : IndepFun
        (fun ω => Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω) * Complex.I))
        (fun ω => Complex.exp (↑ξ * ↑(pieceSum K X f (n + 1) ω) * Complex.I)) μ :=
      (indepFun_partialPieceSum_pieceSum hd hf n).comp hgmeas hgmeas
    calc ∫ ω, Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 2), pieceSum K X f k ω) * Complex.I) ∂μ
        = ∫ ω,
            Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω) * Complex.I)
              * Complex.exp (↑ξ * ↑(pieceSum K X f (n + 1) ω) * Complex.I) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall hexp)
      _ = (∫ ω,
              Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω) * Complex.I) ∂μ)
            * ∫ ω, Complex.exp (↑ξ * ↑(pieceSum K X f (n + 1) ω) * Complex.I) ∂μ :=
          hind.integral_fun_mul_eq_mul_integral hmL.aestronglyMeasurable hmR.aestronglyMeasurable
      _ = (∏ k ∈ Finset.range (n + 1),
              Complex.exp (∫ x in prmPiece (volume.prod ν) k,
                (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(volume.prod ν)))
            * Complex.exp (∫ x in prmPiece (volume.prod ν) (n + 1),
                (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(volume.prod ν)) := by
          rw [ih, integral_exp_pieceSum hd hf ξ (n + 1)]
      _ = ∏ k ∈ Finset.range (n + 2),
            Complex.exp (∫ x in prmPiece (volume.prod ν) k,
              (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(volume.prod ν)) :=
          (Finset.prod_range_succ _ _).symm
