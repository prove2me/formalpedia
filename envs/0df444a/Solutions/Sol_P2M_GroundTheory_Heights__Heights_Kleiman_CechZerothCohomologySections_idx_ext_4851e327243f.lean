-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_idx_ext_4851e327243f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:09:50.964976+00:00
-- url     : https://prove2.me/submissions/450c6ca1-f923-4549-8951-0431c0df18a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechH0SectionsHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsMemSupport

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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections
theorem _root_.solution {U : Finset (Fin (N + 1))} {i : ℕ} {K K' : Cech.Idx U i} (h : K.1.1 = K'.1.1) :
    K = K' :=
  Subtype.ext (Subtype.ext h)
end GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections
