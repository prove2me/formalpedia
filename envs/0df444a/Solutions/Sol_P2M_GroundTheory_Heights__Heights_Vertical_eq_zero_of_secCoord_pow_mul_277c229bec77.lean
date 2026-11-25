-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_eq_zero_of_secCoord_pow_mul_277c229bec77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:12.731412+00:00
-- url     : https://prove2.me/submissions/bb7c617d-3cd1-46a7-8d24-a7b6598c997d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBTorsionFree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_span_secCoord_eq_top_da435bac7731

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
theorem _root_.solution (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R)
    (b : SecAlg Q y) (h : ∀ j, ∃ N : ℕ, secCoord Q y j ^ N * b = 0) : b = 0 := by
  choose N hN using h
  have htop := Ideal.span_pow_eq_top _ (span_secCoord_eq_top Q y) (∑ j, N j)
  have hle : Ideal.span ((fun z => z ^ (∑ j, N j)) '' Set.range (secCoord Q y)) ≤
      LinearMap.ker (LinearMap.mulRight (SecAlg Q y) b) := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.mulRight_apply]
    rw [← Nat.sub_add_cancel (Finset.single_le_sum (fun k _ => Nat.zero_le (N k)) (Finset.mem_univ j)),
      pow_add, mul_assoc, hN j, mul_zero]
  have h1 : (1 : SecAlg Q y) ∈ LinearMap.ker (LinearMap.mulRight (SecAlg Q y) b) :=
    hle (by rw [htop]; exact Submodule.mem_top)
  simpa using h1
end GroundTheory.Heights₂.Heights.Vertical
