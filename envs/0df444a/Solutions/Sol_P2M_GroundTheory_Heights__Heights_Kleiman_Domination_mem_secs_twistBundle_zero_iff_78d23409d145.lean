-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_secs_twistBundle_zero_iff_78d23409d145
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:10:12.016424+00:00
-- url     : https://prove2.me/submissions/bf6bb54d-f778-4d02-99de-2316bc43c570

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
variable {i : Fin (N + 1)} (hi : x i ≠ 0) {j : Fin (N' + 1)} (hj : x' j ≠ 0)
omit [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.Domination
theorem _root_.solution {R : Type*} [CommRing R] [Algebra R Ω] (z : Ω) :
    z ∈ (twistBundle R x' 0).secs ↔ ∀ J : Chart x', z ∈ chartRing R x' J := by
  simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]
  exact forall_congr' fun J => mem_twistMod_zero_iff J z
end GroundTheory.Heights₂.Heights.Kleiman.Domination
