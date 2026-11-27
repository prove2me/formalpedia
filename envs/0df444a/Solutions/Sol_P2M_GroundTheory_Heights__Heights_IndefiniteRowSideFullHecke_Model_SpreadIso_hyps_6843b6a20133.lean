-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_SpreadIso_hyps_6843b6a20133
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:59:27.134104+00:00
-- url     : https://prove2.me/submissions/5bfe907b-11af-4fdb-921b-35eedbfb8cb3

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isFiniteTypeOverZ_specInt_2ea15994c44a

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
open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace SpreadIso
theorem _root_.solution :
    IsFiniteTypeOverZ specInt ∧ 0 < 2 ∧ IsVectorBundle (𝟙_ (invOpen specInt 2).toScheme.Modules) ∧
    Nonempty ((Scheme.Modules.pullback (genRes specInt 2)).obj (𝟙_ (invOpen specInt 2).toScheme.Modules) ≅
      (Scheme.Modules.pullback (genRes specInt 2)).obj (𝟙_ (invOpen specInt 2).toScheme.Modules)) :=
  ⟨isFiniteTypeOverZ_specInt, two_pos, isVectorBundle_unit _, ⟨Iso.refl _⟩⟩
end SpreadIso
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
