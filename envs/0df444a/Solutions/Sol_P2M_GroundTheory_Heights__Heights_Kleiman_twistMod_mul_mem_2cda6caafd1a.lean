-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_mul_mem_2cda6caafd1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:56:51.516275+00:00
-- url     : https://prove2.me/submissions/9bfe376e-3f1c-4b0e-8f26-eaebcc231a08

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PZeroIdealChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_sub_mul_ed3d7223ab6a


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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {K : Chart x} {a b : Ω} {c c' : ℤ} (ha : a ∈ twistMod S x c K)
    (hb : b ∈ twistMod S x c' K) : a * b ∈ twistMod S x (c + c') K := by
  have h := Submodule.mul_mem_mul (M := (twistSys S x c).sub K) (N := (twistSys S x c').sub K) ha hb
  rw [twistSys_sub_mul] at h
  exact h
end GroundTheory.Heights₂.Heights.Kleiman
