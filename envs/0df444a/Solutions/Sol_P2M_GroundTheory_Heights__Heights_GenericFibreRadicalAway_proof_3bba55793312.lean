-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFibreRadicalAway_proof_3bba55793312
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:54:45.912033+00:00
-- url     : https://prove2.me/submissions/38cf4c2f-1839-46ca-b024-5f4ef438046b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RadicalAwayRabinowitsch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFibreRadicalAway
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isRadicalAway_iff_isRadical_rabinowitschIdeal_06c1b40e5723
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_rabinowitschIdeal_map_994460cd29d0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace GenericFibreRadicalAway
theorem _root_.solution (hR : GenericFibreRadical.Statement) :
    GenericFibreRadicalAway.Statement := by
  intro σ _ n K g hK
  obtain ⟨F, hF0, hF⟩ := hR σ (Option (Fin n)) (rabinowitschIdeal K g)
    ((isRadicalAway_iff_isRadical_rabinowitschIdeal K g).1 hK)
  refine ⟨F, hF0, fun t ht => ?_⟩
  have h := hF t ht
  rw [rabinowitschIdeal_map] at h
  exact (isRadicalAway_iff_isRadical_rabinowitschIdeal (fibreIdeal K t) _).2 h
end GenericFibreRadicalAway
end GroundTheory.Heights₂.Heights
