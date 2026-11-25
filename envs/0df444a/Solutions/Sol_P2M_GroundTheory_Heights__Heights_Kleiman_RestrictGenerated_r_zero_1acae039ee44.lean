-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_r_zero_1acae039ee44
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:19:43.656469+00:00
-- url     : https://prove2.me/submissions/d1c8f667-f86b-4b60-be9b-f2e8ca79a9db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictGenerated

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
open GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}
  {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
theorem _root_.solution {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (J : Chart y) : r 0 = 0 := by
  have := h.add J 0 (Q.sub _).zero_mem 0 (Q.sub _).zero_mem
  rw [add_zero] at this
  simpa using this
end GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
