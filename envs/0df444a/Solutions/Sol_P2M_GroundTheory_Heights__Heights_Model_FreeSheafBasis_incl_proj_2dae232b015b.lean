-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_incl_proj_2dae232b015b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:47.649795+00:00
-- url     : https://prove2.me/submissions/904ff22e-b1fe-49bf-a90e-76deedc0bb28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsFreeSheafBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PFreeSheafBasis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis___projC_ac457d736909

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
variable (Y : Scheme.{u}) (n : ℕ)
namespace GroundTheory.Heights₂.Heights.Model.FreeSheafBasis
theorem _root_.solution (i j : Fin n) :
    incl Y n i ≫ proj Y n j = if i = j then 𝟙 (structureModule Y) else 0 :=
  ι_projC (C := SheafOfModules.{u} Y.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf) n i j
end GroundTheory.Heights₂.Heights.Model.FreeSheafBasis
