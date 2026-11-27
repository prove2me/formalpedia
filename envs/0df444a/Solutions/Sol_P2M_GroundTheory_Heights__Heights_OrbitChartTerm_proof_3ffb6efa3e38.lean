-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartTerm_proof_3ffb6efa3e38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:07:34.581512+00:00
-- url     : https://prove2.me/submissions/712a451c-f474-4a32-af25-e084eac09ffe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartTerm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval__mul_block_of_isMultiHomog_db091611cf8f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coe_chartEval_289cf14dcdc3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_ne_zero_of_notMem_orbitIdeal_a02cd0c741c7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coe_evalCone_coordVec_1ad214d3b804
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermLine_toGeo_a_e5f916118ff1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_X_mem_orbitCenter_0f3e436ccb1d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ratioField_le_coordField_177461042b61


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
variable {ι : Type} [Fintype ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
namespace OrbitChartTerm
theorem _root_.solution : OrbitChartTerm.Statement := by
  intro ι _ _ n A x s hs c hxc
  obtain ⟨a, ha, hhom, hW⟩ := hs
  have hfac : evalCone x s =
      ((chartEval x c s : ratioField x) : AlgebraicClosure ℚ) * ∏ k, x k (c k) ^ a k := by
    rw [coe_chartEval, aeval_def, ← eval₂_mul_block_of_isMultiHomog s a hhom _
      (fun p ↦ x p.1 p.2 / x p.1 (c p.1)) (fun k ↦ x k (c k)), evalCone]
    congr 1
    funext p
    exact (div_mul_cancel₀ _ (hxc p.1)).symm
  have hx0 : evalCone x s ≠ 0 := evalCone_ne_zero_of_notMem_orbitIdeal x s a hhom hW
  have hf0 : chartEval x c s ≠ 0 := by
    intro h
    rw [h] at hfac
    simp at hfac
    exact hx0 hfac
  refine ⟨hf0, fun v hv ↦ ?_⟩
  have hsup : ∀ k, ⨆ i, v (coordVec x k i) = v (coordVec x k (c k)) := fun k ↦
    le_antisymm (not_lt.mp fun h ↦ hv k (X_mem_orbitCenter x v k (c k) h))
      (le_ciSup (f := fun i ↦ v (coordVec x k i)) (Finite.bddAbove_range _) (c k))
  have hK : evalCone (coordVec x) s =
      IntermediateField.inclusion (ratioField_le_coordField x) (chartEval x c s) *
        ∏ k, coordVec x k (c k) ^ a k := by
    apply Subtype.ext
    rw [coe_evalCone_coordVec, hfac, MulMemClass.coe_mul, IntermediateField.coe_prod,
      IntermediateField.coe_inclusion]
    simp only [SubmonoidClass.coe_pow]
    rfl
  have hc0 : ∀ k, 0 < v (coordVec x k (c k)) := fun k ↦
    FinitePlace.pos_iff.mpr fun h ↦ hxc k (congrArg Subtype.val h)
  have hv0 : 0 < v (IntermediateField.inclusion (ratioField_le_coordField x) (chartEval x c s)) :=
    FinitePlace.pos_iff.mpr fun h ↦ hf0 (Subtype.ext
      ((IntermediateField.inclusion (ratioField_le_coordField x)).injective
        (h.trans (map_zero _).symm)))
  have ha' : ∀ k, (A.deg k : ℝ) = (a k : ℝ) := fun k ↦ by
    have h := ha k
    rw [HermLine.toGeo_a] at h
    exact_mod_cast h
  rw [hK, map_mul, map_prod, Real.log_mul hv0.ne' (Finset.prod_pos fun k _ ↦ (by
      rw [map_pow]; exact pow_pos (hc0 k) _)).ne',
    Real.log_prod fun k _ ↦ (by rw [map_pow]; exact (pow_pos (hc0 k) _).ne'), finiteTerm]
  simp only [map_pow, Real.log_pow, hsup, ha']
  ring
end OrbitChartTerm
end GroundTheory.Heights₂.Heights
