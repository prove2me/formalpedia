-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_not_isCohenMacaulayAt_top_c9abc576e759
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:09:28.208929+00:00
-- url     : https://prove2.me/submissions/bdfc335d-fa55-427f-b7a2-c653a7a521c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects

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
open MvPolynomial Matrix ComplexSets IsLocalRing
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (q : Fin n → ℂ) :
    ¬ IsCohenMacaulayAt (⊤ : Ideal (MvPolynomial (Fin n) ℂ)) q := by
  intro h
  unfold IsCohenMacaulayAt localRingAt at h
  rw [Ideal.map_top] at h
  have hs : Subsingleton (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) ⧸
      (⊤ : Ideal (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))))) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  obtain ⟨a, b, hab⟩ := h.toIsLocalRing.toNontrivial.exists_pair_ne
  exact hab (Subsingleton.elim a b)
end GroundTheory.Heights₂.Heights
