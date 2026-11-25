-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_pow_zero_sub_58264d6a7b2c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:53.351528+00:00
-- url     : https://prove2.me/submissions/2bf22bc1-f0a0-4643-aaf6-7e1087e776c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NotTwistFiniteAtZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistPowZeroSub
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mul_eq_twist_18fb89964ed5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_pow_zero_sub_b7a88b6ce0bd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution (G B : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) :
    ((G.twist (B.pow 0)).sub I).restrictScalars S = (G.sub I).restrictScalars S := by
  rw [← mul_eq_twist]
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro g hg a ha
    rw [Submodule.restrictScalars_mem, pow_zero_sub] at ha
    rw [Submodule.restrictScalars_mem] at hg ⊢
    rw [mul_comm]
    exact Submodule.smul_mem _ (⟨a, ha⟩ : Kleiman.chartRing S x I) hg
  · intro g hg
    have h1 : (1 : Ω) ∈ ((B.pow 0).sub I).restrictScalars S := by
      rw [Submodule.restrictScalars_mem, pow_zero_sub]
      exact one_mem _
    simpa using Submodule.mul_mem_mul hg h1
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
