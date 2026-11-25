-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_chartEquiv_mk_22d16b1d6585
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:55:24.650838+00:00
-- url     : https://prove2.me/submissions/a74a918e-027c-455c-8ebb-5eaed43b6dd3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PRestrictQuotX

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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}
namespace GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot
theorem _root_.solution {L : LineBundle S x} {L' : LineBundle S y} {r : Ω → K'}
    (h : RestrictData L.toSubSystem hxy L'.toSubSystem r) {pp : Ideal (Poly S N)}
    (hpy : primeOf (S := S) y = pp) (J : Chart y) (z : L.sub (liftChart hxy J)) :
    chartEquiv h hpy J (Submodule.Quotient.mk z) = chartMap h J z := by
  simp [chartEquiv]
end GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot
