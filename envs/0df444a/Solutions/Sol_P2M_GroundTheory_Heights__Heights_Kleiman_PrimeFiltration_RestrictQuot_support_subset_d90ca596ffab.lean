-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_support_subset_d90ca596ffab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:46:35.583009+00:00
-- url     : https://prove2.me/submissions/da137e2c-f37f-4aab-9771-e4f4181c494f

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
theorem _root_.solution (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) : support y ⊆ support x :=
  fun i hi => (mem_support x).mpr (hxy i ((mem_support y).mp hi))
end GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot
