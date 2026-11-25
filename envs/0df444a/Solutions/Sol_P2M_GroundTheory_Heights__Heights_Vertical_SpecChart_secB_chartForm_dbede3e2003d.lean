-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_secB_chartForm_dbede3e2003d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:24:15.075845+00:00
-- url     : https://prove2.me/submissions/a27d1ae0-c6e4-4601-81ce-1850c103f68b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso

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
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
  (j : Fin n)
variable (W : Ideal (MvPolynomial (Fin n) (𝓞 K)))
variable {I W}
variable {v : HeightOneSpectrum (𝓞 K)}
namespace GroundTheory.Heights₂.Heights.Vertical.SpecChart
theorem _root_.solution :
    ∑ m, algebraMap (ParDVR e n v) (SecB e I v) (parY e n v (.inr m)) * toSecB e I v (X m) = 1 := by
  have h : Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (chartForm (parY e n v)) = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  rw [← h, chartForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  congr 1
  simp [toSecB]
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
