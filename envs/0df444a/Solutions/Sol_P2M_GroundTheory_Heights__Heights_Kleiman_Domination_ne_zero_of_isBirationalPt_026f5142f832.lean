-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_ne_zero_of_isBirationalPt_026f5142f832
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:34:38.351976+00:00
-- url     : https://prove2.me/submissions/082f8007-3b3c-4e71-82b9-5928542eb131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination

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
open GroundTheory.Heights₂.Heights.Kleiman.Domination
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}
omit [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.Domination
theorem _root_.solution [Algebra S Ω] {y : Fin (N' + 1) → Ω} (h : IsBirationalPt S y) :
    y ≠ 0 := by
  obtain ⟨I, -⟩ := h 0
  obtain ⟨j, hj⟩ := I.2.1
  intro hy
  exact (mem_support y).mp (I.2.2 hj) (by rw [hy]; rfl)
end GroundTheory.Heights₂.Heights.Kleiman.Domination
