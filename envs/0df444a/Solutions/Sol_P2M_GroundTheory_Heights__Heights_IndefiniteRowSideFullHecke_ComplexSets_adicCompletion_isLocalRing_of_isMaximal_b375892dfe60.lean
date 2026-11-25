-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_adicCompletion_isLocalRing_of_isMaximal_b375892dfe60
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:32:41.074799+00:00
-- url     : https://prove2.me/submissions/a62cac2b-91f3-4134-adeb-6f1d8444d336

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ArtinHenselCompletionNoetherian
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFD
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAffineCompletionNormal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatNormalFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibresRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAffineCompletionNormal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {A : Type*} [CommRing A] (m : Ideal A) [m.IsMaximal]
    (fg : m.FG) : IsLocalRing (AdicCompletion m A) := by
  have := AdicCompletion.isMaximal_map_of_le m m le_rfl fg
  have := AdicCompletion.isAdicComplete_self m fg
  exact isLocalRing_of_isAdicComplete_maximal (m.map (algebraMap A (AdicCompletion m A)))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
