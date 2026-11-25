-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_unitsInflationCochains_comp_cochainsComplex__ce27b045f400
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:27.427459+00:00
-- url     : https://prove2.me/submissions/1eddfb87-2a40-4860-bcfb-a0fb778d6fc8

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisCohomology_UnitsInflationCochainsFHomApply
import Theorems.Thm_GroundTheory_ProfCoh_unitsRestrictHom_hom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_openNormalSubgroupEquiv_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
attribute [local simp] GroundTheory.ProfCoh.coe_openNormalSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer
attribute [local simp] GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21


attribute [local simp] GroundTheory.ProfCoh.unitsRestrictHom_hom_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory groupCohomology
universe u
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable {K L}
variable [IsGalois K L]
namespace GroundTheory.ProfCoh
theorem _root_.solution (E : IntermediateField K L)
    [FiniteDimensional K E] [Normal K E] :
    unitsInflationCochains E ≫ cochainsComplexι (galUnits.{u} K L) =
      groupCohomology.cochainsMap (AlgEquiv.restrictNormalHom E) (unitsRestrictHom E) := by
  ext n : 1
  exact unitsInflationCochainsX_comp_ι E n
end GroundTheory.ProfCoh
