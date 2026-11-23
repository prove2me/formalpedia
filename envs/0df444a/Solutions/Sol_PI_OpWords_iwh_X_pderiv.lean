-- Prove2me | solution 1 for PI.OpWords.iwh_X_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:23.701704+00:00
-- url     : https://prove2.me/submissions/640e1234-11fd-4bb6-9df3-8394295c01de

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
namespace PI.OpWords
theorem _root_.solution {σ : Type} {K : Type} [Field K] (w : σ → ℕ) (i j : σ) (hij : w i = w j)
    {f : MvPolynomial σ K} {n : ℕ} (hf : IsWeightedHomogeneous w f n) :
    IsWeightedHomogeneous w (X i * pderiv j f) n := by
  classical
  rw [f.as_sum, map_sum, Finset.mul_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  have hwm : weight w m = n := hf (MvPolynomial.mem_support_iff.1 hm)
  rw [pderiv_monomial]
  by_cases hmj : m j = 0
  · simp [hmj, isWeightedHomogeneous_zero]
  · have hle : Finsupp.single j 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      omega
    have hs : ∀ v, weight w (Finsupp.single v 1) = w v := by
      intro v
      simp [Finsupp.weight_apply, Finsupp.sum_single_index]
    have h1 : weight w (m - Finsupp.single j 1) + w j = n := by
      rw [← hs j, ← map_add, tsub_add_cancel_of_le hle, hwm]
    rw [X, monomial_mul, one_mul]
    apply isWeightedHomogeneous_monomial
    rw [map_add, hs i, hij, add_comm, h1]
end PI.OpWords
