-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_localizedModule_quotient_79d7d8dcab70
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:23:17.832537+00:00
-- url     : https://prove2.me/submissions/4438a667-3623-4048-9f0f-33a6152eff57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PLengthDecomp
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_localizedModule_eq_of_isLocalizedModule_efd0ccbc6ab4

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
open GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
open Classical
variable {B : Type*} [CommRing B]
namespace GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
theorem _root_.solution (n m : MaximalSpectrum B) :
    length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl (B ⧸ m.asIdeal)) =
      if n = m then 1 else 0 := by
  have hn := n.isMaximal
  have hm := m.isMaximal
  split_ifs with h
  · subst h
    rw [length_localizedModule_eq_of_isLocalizedModule n.asIdeal
      (n.asIdeal.toLocalizedQuotient' (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl
        (Algebra.linearMap B (Localization.AtPrime n.asIdeal)))]
    have hmax : n.asIdeal.localized' (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl
        (Algebra.linearMap B (Localization.AtPrime n.asIdeal)) =
          maximalIdeal (Localization.AtPrime n.asIdeal) := by
      rw [Submodule.localized'_eq_span, ← Localization.AtPrime.map_eq_maximalIdeal]
      rfl
    rw [hmax]
    have : IsSimpleModule (Localization.AtPrime n.asIdeal)
        (Localization.AtPrime n.asIdeal ⧸ maximalIdeal (Localization.AtPrime n.asIdeal)) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
    exact Module.length_eq_one _ _
  · rw [Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
    obtain ⟨s, hsm, hsn⟩ : ∃ s ∈ m.asIdeal, s ∉ n.asIdeal := by
      by_contra! hc
      exact h (MaximalSpectrum.ext (hm.eq_of_le hn.ne_top hc).symm)
    intro x
    refine ⟨s, hsn, ?_⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hsm,
      zero_mul]
end GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
