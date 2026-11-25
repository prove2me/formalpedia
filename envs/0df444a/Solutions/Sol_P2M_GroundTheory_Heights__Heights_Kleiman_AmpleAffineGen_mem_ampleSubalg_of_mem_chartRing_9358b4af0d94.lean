-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_mem_ampleSubalg_of_mem_chartRing_9358b4af0d94
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:12:59.347346+00:00
-- url     : https://prove2.me/submissions/964f8e1e-ccb4-4aa5-ac33-16920b4fef2b

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
theorem _root_.solution {H : SubSystem S x Ω} {m : ℕ} {h : Ω} {I : Chart x}
    (hh : h ∈ (H.pow m).sub I) {a : Ω} (ha : a ∈ chartRing S x I) : a ∈ ampleSubalg H m h I hh :=
  ⟨0, by
    rw [pow_zero, mul_one, Nat.mul_zero]
    change _ ∈ twistMod S x 0 I
    have := Submodule.smul_mem (twistMod S x 0 I) (⟨a, ha⟩ : chartRing S x I)
      (one_mem_twistMod_zero I)
    rwa [chartRing_smul_def, mul_one] at this⟩
end GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
