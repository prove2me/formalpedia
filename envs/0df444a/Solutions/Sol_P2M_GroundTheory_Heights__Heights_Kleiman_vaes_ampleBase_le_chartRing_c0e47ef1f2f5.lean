-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_vaes_ampleBase_le_chartRing_c0e47ef1f2f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:21:52.48278+00:00
-- url     : https://prove2.me/submissions/c563aead-26c9-48d7-b3eb-d65b2ebe2d1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleEmbedSectionsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleEmbedSections

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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {y : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {r : ℕ} {h : Fin (r + 1) → Ω} {j : Fin (r + 1)} (hj : h j ≠ 0) :
    ampleBase (S := k) h j ≤ chartRing k h (singleChart hj) :=
  Algebra.adjoin_le (by rintro _ ⟨l, rfl⟩; exact (ratio (S := k) hj l).2)
end GroundTheory.Heights₂.Heights.Kleiman
