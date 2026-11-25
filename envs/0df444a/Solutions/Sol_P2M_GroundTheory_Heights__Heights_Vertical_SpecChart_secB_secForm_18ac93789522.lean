-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_secB_secForm_18ac93789522
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:24:18.866121+00:00
-- url     : https://prove2.me/submissions/64070c41-fa34-4778-b211-cbb7c28dc65d

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
theorem _root_.solution (i : Fin e) :
    ∑ m, algebraMap (ParDVR e n v) (SecB e I v) (parY e n v (.inl (i, m))) * toSecB e I v (X m) = 0 := by
  have h : Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (secForm (parY e n v) i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
  rw [← h, secForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  congr 1
  simp [toSecB]
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
