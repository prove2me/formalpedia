-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis___projC_ac457d736909
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:20.844665+00:00
-- url     : https://prove2.me/submissions/63e92428-eaf8-4701-979e-fc56b13c7bc1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsFreeSheafBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PFreeSheafBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Model.FreeSheafBasis
variable {C : Type*} [Category C] [Preadditive C] (A : C) (n : ℕ)
  [HasCoproduct (fun _ : ULift.{u} (Fin n) => A)]
namespace GroundTheory.Heights₂.Heights.Model.FreeSheafBasis
theorem _root_.solution (i j : Fin n) :
    Sigma.ι (fun _ : ULift.{u} (Fin n) => A) (ULift.up i) ≫ projC A n j =
      if i = j then 𝟙 A else 0 :=
  Sigma.ι_desc _ _
end GroundTheory.Heights₂.Heights.Model.FreeSheafBasis
