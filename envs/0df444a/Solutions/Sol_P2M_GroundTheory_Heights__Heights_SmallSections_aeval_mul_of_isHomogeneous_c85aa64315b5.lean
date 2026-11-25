-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SmallSections_aeval_mul_of_isHomogeneous_c85aa64315b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:16:55.435214+00:00
-- url     : https://prove2.me/submissions/b168a7da-a6ba-4821-b59e-96e4e639d649

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SmallSections
theorem _root_.solution {σ A : Type*} [CommRing A] [Algebra ℤ A] {F : MvPolynomial σ ℤ} {τ : ℕ}
    (hF : F.IsHomogeneous τ) (t : A) (x : σ → A) :
    aeval (fun j ↦ t * x j) F = t ^ τ * aeval x F := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, aeval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ ↦ ?_
  have hw : (μ.sum fun _ e ↦ e) = τ := by
    have h := hF (mem_support_iff.mp hμ)
    rw [Finsupp.weight_apply] at h
    simpa using h
  rw [← hw]
  simp only [Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring
end GroundTheory.Heights₂.Heights.SmallSections
