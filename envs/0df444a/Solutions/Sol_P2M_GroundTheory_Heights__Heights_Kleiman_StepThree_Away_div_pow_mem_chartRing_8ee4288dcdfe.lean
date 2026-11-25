-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_div_pow_mem_chartRing_8ee4288dcdfe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:10:36.576649+00:00
-- url     : https://prove2.me/submissions/439af4cd-aedc-490f-9df5-72ac16d4207d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway

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
open GroundTheory.Heights₂.Heights.Kleiman.StepThree GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
theorem _root_.solution (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) {h : Poly S N} {d : ℕ}
    (hh : h.IsHomogeneous d) : aeval x h / x i ^ d ∈ chartRing S x I :=
  ⟨h, X i ^ d, d, pow_mem (X_mem_monos hi) d, hh, isHomogeneous_X_pow i d, by rw [map_pow, aeval_X]⟩
end GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
