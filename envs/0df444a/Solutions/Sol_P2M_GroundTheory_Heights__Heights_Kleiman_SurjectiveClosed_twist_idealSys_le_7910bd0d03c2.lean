-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_twist_idealSys_le_7910bd0d03c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:58:22.368814+00:00
-- url     : https://prove2.me/submissions/7d0869a0-5d47-451b-ad5e-cf8dfbaa15d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_twist_sub_eq_mul_482b06edabb9

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
open GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
theorem _root_.solution (F : SubSystem S x Ω) (J : Ideal (Poly S N)) (I : Chart x) :
    (F.twist (idealSys x J)).sub I ≤ F.sub I := by
  rw [twist_sub_eq_mul]
  refine Submodule.mul_le.mpr fun a ha y hy => ?_
  have ha' : a ∈ idealMod (x := x) J I := ha
  have : ∃ b : chartRing S x I, (b : Ω) = a := by
    refine Submodule.span_induction (p := fun a _ => ∃ b : chartRing S x I, (b : Ω) = a) ?_ ?_ ?_ ?_
      ha'
    · rintro _ ⟨f, s, e, _, hs, hfe, hse, rfl⟩
      exact ⟨⟨_, f, s, e, hs, hfe, hse, rfl⟩, rfl⟩
    · exact ⟨0, rfl⟩
    · rintro _ _ _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
      exact ⟨b + b', rfl⟩
    · rintro r _ _ ⟨b, rfl⟩
      exact ⟨r * b, rfl⟩
  obtain ⟨b, rfl⟩ := this
  exact (F.sub I).smul_mem b hy
end GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
