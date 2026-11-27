-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_equiv_119cab424104
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:59:48.619419+00:00
-- url     : https://prove2.me/submissions/a99e7a90-a576-4d44-b415-0b27bdea31ff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteTypeSectionsOfIsFiniteTypeOverZ
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_alg_iff_05d37dae7f6f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_scheme_of_alg_f4618e49e8db
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_FiniteIntegralClosure_normalization_of_scheme_88130ec41a00

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace FiniteIntegralClosure
theorem _root_.solution :
    (_root_.GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.Statement ∧
      _root_.GroundTheory.Heights₂.Heights.Model.FiniteNormalization.Statement) ↔
    FiniteIntegralClosure.Statement := by
  constructor
  · rintro ⟨ha, -⟩
    have hb := FiniteIntegralClosure.alg_iff.mp ha
    exact ⟨hb, FiniteIntegralClosure.scheme_of_alg hb⟩
  · rintro ⟨hb, hs⟩
    exact ⟨FiniteIntegralClosure.alg_iff.mpr hb, FiniteIntegralClosure.normalization_of_scheme hs⟩
end FiniteIntegralClosure
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
