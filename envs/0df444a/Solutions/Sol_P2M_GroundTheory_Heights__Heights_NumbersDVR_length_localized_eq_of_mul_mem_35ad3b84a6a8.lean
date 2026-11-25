-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localized_eq_of_mul_mem_35ad3b84a6a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:40.712851+00:00
-- url     : https://prove2.me/submissions/dbeeb959-1963-404f-8433-08b7adfdb59b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localized_eq_of_le_39c21971b573

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
variable {A : Type*} [CommRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {J J' W : Ideal A} [W.IsPrime] {s t : A} (hs : s ∉ W)
    (ht : t ∉ W) (hsJ : ∀ x ∈ J, s * x ∈ J') (htJ : ∀ x ∈ J', t * x ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J')) := by
  have key : ∀ {J J' : Ideal A} {t : A}, t ∉ W → (∀ x ∈ J', t * x ∈ J) →
      ∀ x ∈ J ⊔ J', ∃ t ∉ W, t * x ∈ J := by
    intro J J' t ht htJ x hx
    obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hx
    exact ⟨t, ht, by rw [mul_add]; exact J.add_mem (J.mul_mem_left t ha) (htJ a' ha')⟩
  rw [length_localized_eq_of_le le_sup_left (key ht htJ),
    length_localized_eq_of_le le_sup_left (key hs hsJ), sup_comm]
end GroundTheory.Heights₂.Heights.NumbersDVR
