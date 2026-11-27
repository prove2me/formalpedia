-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OneBlockModel_proof_dbba04e4af05
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:07:41.622026+00:00
-- url     : https://prove2.me/submissions/cd6b025d-bc1e-409d-8795-456120b0b0ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_algebraicIndependent_genericT_3541f30eb225
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeCoord_ne_zero_0edf84f2cbfa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_genericT_mem_adjoin_de0e759ca5b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_ratios_isAlgebraic_ffea12827701
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_birational_latticeCoord_528f8b6c0df6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeMap_image_homogeneous_5a8f9f7890e0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_mCoordIdeal_latticeCoord_f0c94eca4f56


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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights
namespace OneBlockModel
theorem _root_.solution (hCC : CoordConeArithVar.Statement) : OneBlockModel.Statement := by
  intro K _ _ r N F φ hφ
  refine ⟨⟨LatticeModel.latticeVariety φ hφ, rfl⟩, LatticeModel.mCoordIdeal_latticeCoord φ, ?_,
    LatticeModel.birational_latticeCoord F.fg hφ, fun m hm ↦ LatticeModel.latticeMap_image_homogeneous hφ hm⟩
  rw [← LatticeModel.mCoordIdeal_latticeCoord φ]
  exact hCC Unit (blockIdx fun _ : Unit ↦ N) (LatticeField K r) (latticeCoord φ) (fun _ ↦ 0) r
    (LatticeModel.genericT K r) ⟨()⟩ (fun _ ↦ LatticeModel.latticeCoord_ne_zero hφ 0)
    LatticeModel.algebraicIndependent_genericT (LatticeModel.genericT_mem_adjoin F.fg hφ)
    LatticeModel.ratios_isAlgebraic
end OneBlockModel
end GroundTheory.Heights₂.Heights
