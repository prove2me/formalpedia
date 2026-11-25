-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_coord_le_len_29a8affd8563
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:52:39.372096+00:00
-- url     : https://prove2.me/submissions/e4950cc4-341a-4f05-9230-e94097c30c37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Imports
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CoerciveOfPositiveDefinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLatticePointsBelowFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_coercive_of_posDef_51d8eb336b65
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (g : archUnitary h v) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (y : InfinitePlace E → ι → ℂ) w i,
      ‖y w i‖ ≤ K * M.len (invApply g y) := by
  choose c hc hcoer using fun w => exists_coercive_of_posDef (M.posDef w)
  set G : InfinitePlace E → Matrix ι ι ℂ := fun w =>
    (((g : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) with hG
  refine ⟨∑ w, ∑ i, ∑ j, ‖G w i j‖ / Real.sqrt (c w), by positivity, fun y w i => ?_⟩
  set z := invApply g y with hz
  have hre : ∀ w', 0 ≤ (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re := fun w' =>
    (Complex.nonneg_iff.mp ((M.posDef w').posSemidef.dotProduct_mulVec_nonneg (z w'))).1
  have hinv : G w * (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
    simp [hG]
  have hy : y w = G w *ᵥ z w := by
    rw [hz, invApply, mulVec_mulVec, hinv, one_mulVec]
  have hzj : ∀ j, ‖z w j‖ ≤ M.len z / Real.sqrt (c w) := by
    intro j
    have hsq : 0 < Real.sqrt (c w) := Real.sqrt_pos.2 (hc w)
    rw [le_div_iff₀ hsq]
    have h1 : c w * ‖z w j‖ ^ 2 ≤ ∑ w', (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re :=
      (hcoer w (z w) j).trans (Finset.single_le_sum (fun w' _ => hre w') (Finset.mem_univ w))
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_mul (hc w).le, Real.sqrt_sq (norm_nonneg _)] at h2
    unfold Majorant.len
    linarith
  have hlen : 0 ≤ M.len z := Real.sqrt_nonneg _
  calc ‖y w i‖ = ‖∑ j, G w i j * z w j‖ := by rw [hy]; rfl
    _ ≤ ∑ j, ‖G w i j‖ * ‖z w j‖ := (norm_sum_le _ _).trans (by simp)
    _ ≤ ∑ j, ‖G w i j‖ / Real.sqrt (c w) * M.len z := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [div_mul_eq_mul_div, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (hzj j) (norm_nonneg _)
    _ = (∑ j, ‖G w i j‖ / Real.sqrt (c w)) * M.len z := by rw [Finset.sum_mul]
    _ ≤ (∑ w', ∑ i', ∑ j, ‖G w' i' j‖ / Real.sqrt (c w')) * M.len z := by
        refine mul_le_mul_of_nonneg_right ?_ hlen
        refine le_trans ?_ (Finset.single_le_sum (f := fun w' => ∑ i', ∑ j,
          ‖G w' i' j‖ / Real.sqrt (c w')) (fun _ _ => by positivity) (Finset.mem_univ w))
        exact Finset.single_le_sum (f := fun i' => ∑ j, ‖G w i' j‖ / Real.sqrt (c w))
          (fun _ _ => by positivity) (Finset.mem_univ i)
end GroundTheory.Heights₂.Heights.FiniteCovolume
