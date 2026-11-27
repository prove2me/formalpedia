-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_SupNormEquality_equiv_4ada4e93fda3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:56:21.570607+00:00
-- url     : https://prove2.me/submissions/627a10e7-ec03-4f50-95c9-487c43b079e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isWeightedHomogeneous_unit_iff_07c0a93ceda5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forms_of_block_f0b3b11b368b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_secM_block_9be15845911c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_sSup_eq_of_upperBounds_eq_56a7107924cc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_upperBounds_eq_of_sSup_eq_1bfc466c0f85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_upperBounds_points_a57829176757
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_upperBounds_image_e0da00e43ab5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_bddAbove_points_1b2bf4c62714
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_bddAbove_image_a464d991008c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forall_points_rename_fbb12ff9318c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forall_conePoints_rename_20d6ca4e5ae5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_points_nonempty_iff_cc5ca15a244b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (secM sec IsMultiHomog)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
namespace SupNormEquality
theorem _root_.solution : Heights.SupNormEquality.Statement ↔ IndefiniteRowSideFullHecke.Close.SupNormEquality.Statement := by
  constructor
  · intro hA ι _ _ n P k₀
    refine ⟨fun N ↦ secM_block P k₀ N, fun N f hf ↦ sSup_eq_of_upperBounds_eq ?_⟩
    ext B
    rw [mem_upperBounds_points, mem_upperBounds_image, ← forall_points_rename,
      ← forall_conePoints_rename]
    refine (hA ι n P k₀ N).2 _ ?_ B
    rw [isWeightedHomogeneous_unit_iff]
    exact hf.rename_isHomogeneous
  · intro hB ι _ _ n P k₀ m
    refine ⟨forms_of_block k₀ m, fun f' hf' B ↦ ?_⟩
    have hf'eq : f' = rename (blockCoordEquiv (n := n) k₀)
        (rename (blockCoordEquiv (n := n) k₀).symm f') := by
      rw [rename_rename, Equiv.self_comp_symm, rename_id_apply]
    set f := rename (blockCoordEquiv (n := n) k₀).symm f'
    have hf : f.IsHomogeneous m :=
      ((isWeightedHomogeneous_unit_iff f').mp hf').rename_isHomogeneous
    rw [hf'eq, forall_points_rename, forall_conePoints_rename, ← mem_upperBounds_points,
      ← mem_upperBounds_image]
    rw [upperBounds_eq_of_sSup_eq (bddAbove_points P k₀ hf) (bddAbove_image P k₀ hf)
      (by rw [Set.image_nonempty, Set.image_nonempty]; exact points_nonempty_iff hB P k₀)
      ((hB ι n P k₀).2 m f hf)]
end SupNormEquality
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
