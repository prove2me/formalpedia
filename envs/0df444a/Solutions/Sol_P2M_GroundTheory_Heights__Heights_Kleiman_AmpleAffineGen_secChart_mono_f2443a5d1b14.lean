-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_mono_f2443a5d1b14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:09:53.195177+00:00
-- url     : https://prove2.me/submissions/12be1deb-191e-4f94-bec5-0905612d196d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen

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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
theorem _root_.solution {Q H : SubSystem S x Ω} {m b : ℕ} {h : Ω} {I K : Chart x} (hIK : I.1 ⊆ K.1)
    {z : Ω} (hz : z ∈ secChart Q H m b h I) : z ∈ secChart Q H m b h K :=
  let ⟨k, hk⟩ := hz
  ⟨k, (Q.twist (H.pow (b + m * k))).mono I K hIK _ hk⟩
end GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
