-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_span_secCoord_eq_top_da435bac7731
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:24:57.930492+00:00
-- url     : https://prove2.me/submissions/458c08e7-82f3-482d-919d-b9d9aa4a7429

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBTorsionFree

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
variable {R : Type*} [CommRing R] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) :
    Ideal.span (Set.range (secCoord Q y)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : Ideal.Quotient.mk (secIdeal Q y) (chartForm y - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
  rw [map_sub, map_one, sub_eq_zero] at h1
  have h2 : (1 : SecAlg Q y) = ∑ j, Ideal.Quotient.mk _ (C (y (.inr j))) * secCoord Q y j := by
    rw [← h1, chartForm, linForm, map_sum]
    simp only [map_mul, secCoord]
  rw [h2]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
end GroundTheory.Heights₂.Heights.Vertical
