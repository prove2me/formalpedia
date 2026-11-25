-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_idealMod_loc_beabb2cef896
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:11:36.57516+00:00
-- url     : https://prove2.me/submissions/c05becac-e46b-4bda-a941-d6a60aaf27a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_exists_unit_mul_mem_of_span_3d253f35998c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
theorem _root_.solution {I J : Chart x} (h : I.1 ⊆ J.1) (J' : Ideal (Poly S N)) {y : Ω}
    (hy : y ∈ idealMod J' J) :
    ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧ (a : Ω) * y ∈ idealMod J' I := by
  refine exists_unit_mul_mem_of_span h _ ?_ hy
  rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have hs0 := eval_ne_zero_of_mem_monos J hs
  have hX0 : aeval x (X i ^ e : Poly S N) ≠ 0 := by
    rw [map_pow, aeval_X]; exact pow_ne_zero _ hxi
  refine ⟨⟨aeval x s / aeval x (X i ^ e), s, X i ^ e, e, pow_mem (X_mem_monos hi) e, hse,
    isHomogeneous_X_pow i e, rfl⟩, ?_, ?_⟩
  · rw [isUnit_iff_exists_inv]
    refine ⟨⟨aeval x (X i ^ e) / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow i e, hse, rfl⟩, ?_⟩
    apply Subtype.ext
    change aeval x s / aeval x (X i ^ e) * (aeval x (X i ^ e) / aeval x s) = 1
    field_simp
  · change aeval x s / aeval x (X i ^ e) * (aeval x f / aeval x s) ∈ idealMod J' I
    rw [show aeval x s / aeval x (X i ^ e) * (aeval x f / aeval x s) =
      aeval x f / aeval x (X i ^ e) by field_simp]
    exact Submodule.subset_span ⟨f, X i ^ e, e, hf, pow_mem (X_mem_monos hi) e, hfe,
      isHomogeneous_X_pow i e, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
