-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P17.fisher_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:21:00.438619+00:00
-- url     : https://prove2.me/submissions/a5412f37-fa75-419e-91d2-95599a719c54

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P17
noncomputable section

open Filter MeasureTheory

open scoped ENNReal BigOperators Topology

open QAlgorithms.Papers.Independent.Next46.P17

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P19 (productWeyl FiniteMeanEnergy PhysicalCovariance Cov FockIndex covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

lemma g62h_relEnt_self {I : Type} (A : Matrix I I ℂ) : extendedRelativeEntropyNats A A = 0 := by
  unfold extendedRelativeEntropyNats
  refine le_antisymm (iSup_le fun s => ?_) (zero_le)
  unfold QAlgorithms.Papers.Independent.Frontier18.P07.finiteRelativeEntropy
  simp

lemma g62h_curve_nonneg {I : Type} (rho : ℝ → Matrix I I ℂ) (base θ : ℝ) :
    0 ≤ divergenceCurve rho base θ := ENNReal.toReal_nonneg

lemma g62h_curve_base {I : Type} (rho : ℝ → Matrix I I ℂ) (base : ℝ) :
    divergenceCurve rho base base = 0 := by
  simp [divergenceCurve, g62h_relEnt_self]

theorem solution {I : Type} [Countable I]
    (rho : ℝ → State I) (base : ℝ)
    (h : FisherRegular (fun theta => (rho theta).coefficients) base) :
    0 ≤ fisher (fun theta => (rho theta).coefficients) base := by
  set D := divergenceCurve (fun theta => (rho theta).coefficients) base with hD
  unfold fisher
  rw [← hD]
  by_contra hneg'
  have hneg := not_le.mp hneg'
  have hmin : IsLocalMin D base := Filter.Eventually.of_forall (fun θ => by
    rw [hD, g62h_curve_base]; exact g62h_curve_nonneg _ _ _)
  have hd0 : deriv D base = 0 := hmin.deriv_eq_zero
  have hc : ContinuousAt D base := h.2.1.self_of_nhds.continuousAt
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hd0 hc
  have hzero : D =ᶠ[𝓝 base] fun _ => (0 : ℝ) := by
    filter_upwards [hmax] with θ hθ
    have h1 : D base = 0 := g62h_curve_base _ _
    have h2 := g62h_curve_nonneg (fun theta => (rho theta).coefficients) base θ
    linarith
  have hd : deriv D =ᶠ[𝓝 base] fun _ => (0 : ℝ) := by
    filter_upwards [hzero.eventuallyEq_nhds] with θ hθ
    rw [hθ.deriv_eq]; simp
  rw [hd.deriv_eq] at hneg
  simp at hneg
