-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_cancel_f626b308d17b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:14:29.178725+00:00
-- url     : https://prove2.me/submissions/73d8b046-4130-49c0-9b70-ed0c8e71c159

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_SpreadIsoModelIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_id_4d71231cc7a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_assoc_b3f71914056c

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
variable {T T' Y Z : Scheme.{0}} {F G : Z.Modules}
local notation "along" => GroundTheory.Heights₂.Heights.Model.pullbackIsoAlong
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution {ρ : T' ⟶ T} [IsIso ρ] {k : T ⟶ Z} {k' : T' ⟶ Z} (e : ρ ≫ k = k')
    {φ₁ φ₂ : (Scheme.Modules.pullback k).obj F ≅ (Scheme.Modules.pullback k).obj G}
    (H : along e φ₁ = along e φ₂) : φ₁ = φ₂ := by
  have e' : inv ρ ≫ k' = k := by rw [← e, IsIso.inv_hom_id_assoc]
  have e'' : (inv ρ ≫ ρ) ≫ k = k := by rw [IsIso.inv_hom_id, Category.id_comp]
  have := congrArg (along e') H
  rwa [along_assoc e e' e'', along_assoc e e' e'', along_id (IsIso.inv_hom_id ρ),
    along_id (IsIso.inv_hom_id ρ)] at this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
