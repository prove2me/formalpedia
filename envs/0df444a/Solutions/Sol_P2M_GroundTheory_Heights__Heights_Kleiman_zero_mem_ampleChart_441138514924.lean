-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_zero_mem_ampleChart_441138514924
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:07.003925+00:00
-- url     : https://prove2.me/submissions/bec8c992-c6f5-4370-8a92-c2263580ac23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestriction

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
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {S : Type u} [CommRing S] {E : Type w} [Field E] [Algebra S E] {M : ℕ}
    {z : Fin (M + 1) → E} {H : SubSystem S z E} {σ : E} {I : Chart z} :
    (0 : E) ∈ ampleChart H 1 σ I :=
  ⟨0, by rw [zero_mul]; exact Submodule.zero_mem _⟩
end GroundTheory.Heights₂.Heights.Kleiman
