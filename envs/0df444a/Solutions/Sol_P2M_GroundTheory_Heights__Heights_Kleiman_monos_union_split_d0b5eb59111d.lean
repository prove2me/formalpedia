-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_monos_union_split_d0b5eb59111d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:26:56.434276+00:00
-- url     : https://prove2.me/submissions/c20dfb71-cc16-4551-aa76-933af31b7544

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PZeroIdealChart

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
theorem _root_.solution {I K : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos (I ∪ K)) :
    ∃ u ∈ monos (S := S) I, ∃ v ∈ monos (S := S) K, u * v = s := by
  unfold monos at hs
  rw [Finset.coe_union, Set.image_union, Submonoid.closure_union, Submonoid.mem_sup] at hs
  exact hs
end GroundTheory.Heights₂.Heights.Kleiman
