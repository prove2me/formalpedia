-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P17.fisher_reparametrization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:21:37.895352+00:00
-- url     : https://prove2.me/submissions/aa7b1072-0802-43e2-b1b9-6002b74a17b8

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

theorem solution {I : Type} [Countable I]
    (rho : ℝ → State I) (c base : ℝ)
    (hScale : FisherRegular (fun theta => (rho theta).coefficients) (c * base))
    (hShift : FisherRegular (fun theta => (rho theta).coefficients) (base + c)) :
    fisher (fun theta => (rho (c * theta)).coefficients) base =
        c ^ 2 * fisher (fun theta => (rho theta).coefficients) (c * base) ∧
    fisher (fun theta => (rho (theta + c)).coefficients) base =
        fisher (fun theta => (rho theta).coefficients) (base + c) := by
  constructor
  · unfold fisher
    set f := divergenceCurve (fun theta => (rho theta).coefficients) (c * base)
    have e1 : divergenceCurve (fun theta => (rho (c * theta)).coefficients) base =
        fun θ => f (c * θ) := rfl
    have e2 : deriv (fun θ => f (c * θ)) = fun θ => c * deriv f (c * θ) := by
      funext θ; rw [deriv_comp_mul_left, smul_eq_mul]
    rw [e1, e2, deriv_const_mul_field']
    simp only []
    rw [deriv_comp_mul_left (f := deriv f), smul_eq_mul]
    ring
  · unfold fisher
    set f := divergenceCurve (fun theta => (rho theta).coefficients) (base + c)
    have e1 : divergenceCurve (fun theta => (rho (theta + c)).coefficients) base =
        fun θ => f (θ + c) := rfl
    have e2 : deriv (fun θ => f (θ + c)) = fun θ => deriv f (θ + c) := by
      funext θ; rw [deriv_comp_add_const]
    rw [e1, e2, deriv_comp_add_const]
