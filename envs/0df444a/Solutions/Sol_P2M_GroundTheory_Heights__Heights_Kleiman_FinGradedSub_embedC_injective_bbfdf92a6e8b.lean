-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_embedC_injective_bbfdf92a6e8b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:47:01.00108+00:00
-- url     : https://prove2.me/submissions/b4daf132-4804-4cc3-a019-96929b5bc53f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFinite

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
variable (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ)
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace FinGradedSub
theorem _root_.solution (n : ℕ) : Function.Injective (M.embedC c n) := by
  intro s t hst
  funext K
  have h := congrArg (coeffAt S x c) (congrFun hst (ofChartIdx K))
  rw [M.embedC_of_subset c s (ofChartIdx K) K.1.2.2, M.embedC_of_subset c t (ofChartIdx K) K.1.2.2,
    coeffAt_coneSingle_same, coeffAt_coneSingle_same] at h
  exact Subtype.ext h
end FinGradedSub
end GroundTheory.Heights₂.Heights.Kleiman
