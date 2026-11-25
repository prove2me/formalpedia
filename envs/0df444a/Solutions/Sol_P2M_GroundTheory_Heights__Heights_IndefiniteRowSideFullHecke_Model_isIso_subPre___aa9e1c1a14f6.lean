-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isIso_subPre___aa9e1c1a14f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:14:40.450121+00:00
-- url     : https://prove2.me/submissions/a8492bc1-aed1-42b3-aa4c-c577d41007f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_SpreadIsoModelIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genTo_mem_invOpen_6f185c6bdade
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genRes___bee8f56e8f74

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
open CategoryTheory AlgebraicGeometry
variable (X : Scheme.{0})
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution {a m' : ℕ} (ha : 0 < a) (hm' : 0 < m') :
    IsIso (genRes X a ⁻¹ᵁ subOpen X a m').ι :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by
    rw [Scheme.Opens.opensRange_ι]
    refine top_unique fun x _ => ?_
    show ((genRes X a ≫ (invOpen X a).ι)).base x ∈ invOpen X (a * m')
    rw [genRes_ι]
    exact genTo_mem_invOpen X (Nat.mul_ne_zero ha.ne' hm'.ne') _)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
