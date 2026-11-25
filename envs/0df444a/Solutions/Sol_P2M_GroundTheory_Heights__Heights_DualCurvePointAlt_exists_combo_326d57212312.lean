-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_exists_combo_326d57212312
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:10:50.058158+00:00
-- url     : https://prove2.me/submissions/7b529cc8-28e0-4009-b017-03445cdbe86d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualCurvePoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_linVal_eq_c5bae4ee8eec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualCurvePointAlt_dualLatticeCoord_eq_d4438b97a002
import Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_fg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_int_smul_mem_latticeDual_7ca10bc0ad16


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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualCurvePointAlt
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} [Fintype T]
  [DecidableEq T]
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.DualCurvePointAlt
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice F)) (w : Fin i → K) :
    ∃ (D : ℤ) (c : T → ℤ), D ≠ 0 ∧
      (D : ProjField K i) * linVal w = ∑ t, (c t : ProjField K i) * dualLatticeCoord b ⟨(), t⟩ := by
  obtain ⟨D, hD, hmem⟩ := exists_int_smul_mem_latticeDual F.lattice F.fg w
  have hmem' : D • w ∈ dualLattice F := hmem
  refine ⟨D, b.repr ⟨D • w, hmem'⟩, hD, ?_⟩
  have h : D • w = ∑ t, (b.repr ⟨D • w, hmem'⟩ t) • (b t : Fin i → K) := by
    have := congrArg Subtype.val (b.sum_repr ⟨D • w, hmem'⟩)
    rw [Submodule.coe_sum] at this
    simpa using this.symm
  have hj : ∀ j, (D : K) * w j = ∑ t, (b.repr ⟨D • w, hmem'⟩ t : K) * (b t : Fin i → K) j := fun j => by
    have := congrFun h j
    simpa [Finset.sum_apply, zsmul_eq_mul] using this
  simp only [linVal_eq, dualLatticeCoord_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 := congrArg (constK K i) (hj j)
  simp only [map_mul, map_intCast, map_sum] at h2
  rw [← mul_assoc, h2, Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ => mul_assoc _ _ _
end GroundTheory.Heights₂.Heights.DualCurvePointAlt
