-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_proj_incl_59ea9a70b16f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:53.334014+00:00
-- url     : https://prove2.me/submissions/d31e85d1-0471-4cd5-a3e8-46024214f6b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsFreeSheafBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PFreeSheafBasis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_projC___11ca3dfecaad

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
theorem _root_.solution : ∑ j, proj Y n j ≫ incl Y n j = 𝟙 (freeModule Y n) :=
  sum_projC_ι (C := SheafOfModules.{u} Y.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf) n
end GroundTheory.Heights₂.Heights.Model.FreeSheafBasis
