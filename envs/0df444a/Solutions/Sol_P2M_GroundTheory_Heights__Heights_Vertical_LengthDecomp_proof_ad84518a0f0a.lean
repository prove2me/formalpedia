-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_proof_ad84518a0f0a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:37:46.211655+00:00
-- url     : https://prove2.me/submissions/bbc55eb3-f691-446c-b3a7-8d378705bc85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PLengthDecomp
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_localizedModule_eq_of_isLocalizedModule_efd0ccbc6ab4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_eq_sum_d4330b1b5c31
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_finite_maximalSpectrum_0d05a3129625

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
open Module IsLocalRing LinearMap Submodule
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace LengthDecomp
theorem _root_.solution : LengthDecomp.Statement := by
  intro R B _ _ _ _ _ _ b hfin
  have := LengthDecomp.finite_maximalSpectrum (R := R) (B := B)
  let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  have hB : IsFiniteLength B (B ⧸ Ideal.span {b}) := by
    rw [length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hfin
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact hfin.imp (isNoetherian_of_tower R) (isArtinian_of_tower R)
  rw [LengthDecomp.length_eq_sum (R := R) hB, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  have hspan : (Ideal.span {b}).localized' (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl
      (Algebra.linearMap B (Localization.AtPrime n.asIdeal)) =
        Ideal.span {algebraMap B (Localization.AtPrime n.asIdeal) b} := by
    rw [Ideal.span, Submodule.localized'_span, Set.image_singleton]
    rfl
  rw [Ring.ord, LengthDecomp.length_localizedModule_eq_of_isLocalizedModule n.asIdeal
    ((Ideal.span {b}).toLocalizedQuotient' (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl
      (Algebra.linearMap B (Localization.AtPrime n.asIdeal))), hspan]
end LengthDecomp
end GroundTheory.Heights₂.Heights.Vertical
