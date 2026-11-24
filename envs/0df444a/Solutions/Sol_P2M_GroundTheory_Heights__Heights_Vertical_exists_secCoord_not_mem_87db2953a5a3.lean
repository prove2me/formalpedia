-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_exists_secCoord_not_mem_87db2953a5a3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:58.266457+00:00
-- url     : https://prove2.me/submissions/c1b12816-d719-47b4-9701-ab5d7d1d876d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecIdealOfPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K))
    (J : Ideal (SecB e I v)) (hJ : J ≠ ⊤) : ∃ j, toSecB e I v (X j) ∉ J := by
  by_contra! h
  apply hJ
  rw [Ideal.eq_top_iff_one]
  have h1 : Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (chartForm (parY e n v)) = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  rw [← h1, chartForm, linForm, map_sum]
  refine J.sum_mem fun j _ => ?_
  rw [map_mul]
  refine J.mul_mem_left _ ?_
  simpa [toSecB] using h j
end GroundTheory.Heights₂.Heights.Vertical
