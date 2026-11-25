-- Prove2me | solution 1 for P2M_GroundTheory_Variant__N1_MapThetaTInvariant_sigmaCompactSpace_2f9320bd201b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:44:18.724175+00:00
-- url     : https://prove2.me/submissions/657137c2-e8c9-4ebe-ba63-46674ce17626

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant
import Theorems.Thm_P2M_GroundTheory_Variant__N1_MapThetaTInvariant_countable_valueGroupWithZero_cd8b2c53ac4b
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_transposeHomeo_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.ContragredientTranspose.transposeHomeo_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1
open MeasureTheory Topology Filter ValuativeRel
open GroundTheory.Variant₂.N1.MapThetaTInvariant
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Variant₂.N1.MapThetaTInvariant
theorem _root_.solution : SigmaCompactSpace F := by
  have := countable_valueGroupWithZero F
  refine SigmaCompactSpace.of_countable
    (Set.range fun γ : ValueGroupWithZero F => {x : F | valuation F x ≤ γ})
    (Set.countable_range _) ?_ ?_
  · rintro _ ⟨γ, rfl⟩
    exact IsNonarchimedeanLocalField.isCompact_closedBall F γ
  · ext x
    simp only [Set.sUnion_range, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨_, le_rfl⟩
end GroundTheory.Variant₂.N1.MapThetaTInvariant
