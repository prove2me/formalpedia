-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.topComp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:29:53.095881+00:00
-- url     : https://prove2.me/submissions/77989e6c-bd19-4bdf-bdb9-8534987dfd1e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCCalc
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlock
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopComp
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_top_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_block_part_embedding_first
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_block_part_embedding_second
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_block_part_diagonal_first
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_block_part_diagonal_second
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_g_mX
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_supp_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_bdL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_mX_factor
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_rotL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LVs.TC.rotL_apply


section
noncomputable section
open Matrix
open scoped ContDiff Topology
namespace PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
private theorem eq_mul_mX_mul_mX_blockEntries (g : M2 n) (j : ℕ) (t : Matrix (Fin n) (Fin n) ℂ) :
    g + topL g j t = g * mX 1 ((2 * Complex.I)⁻¹ • matrixBlockRestriction (blkA j) (blkA j) t)
      ((-(2 * Complex.I)⁻¹) • matrixBlockRestriction (blkB j) (blkB j) t) 1 *
      mX (1 + (2 * Complex.I)⁻¹ • matrixBlockRestriction (blkA j) (blkB j) t) 0 0
        (1 + (-(2 * Complex.I)⁻¹) • matrixBlockRestriction (blkB j) (blkA j) t) := by
  rw [mul_assoc, ← mX_factor j _ _ _ _ (supp_smul _ _) (supp_smul _ _) (supp_smul _ _) (supp_smul _ _), g_mX]
  simp only [topL, conjL_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, block_part_linear_apply,
    neg_smul]
private theorem conjL_bdiag_eq_mul_mX_blockEntries (g : M2 n) (j : ℕ) (t : Matrix (Fin n) (Fin n) ℂ) :
    g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0
      (bdiag j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t) =
    g * mX 1 ((2 * Complex.I)⁻¹ • matrixBlockRestriction (blkA j) (blkA j) t)
      ((-(2 * Complex.I)⁻¹) • matrixBlockRestriction (blkB j) (blkB j) t) 1 := by
  have h := g_mX g 0 ((2 * Complex.I)⁻¹ • matrixBlockRestriction (blkA j) (blkA j) t)
    ((-(2 * Complex.I)⁻¹) • matrixBlockRestriction (blkB j) (blkB j) t) 0
  simp only [add_zero] at h
  rw [h, conjL_apply]
  simp only [ContinuousLinearMap.zero_apply, block_part_linear_apply, block_part_diagonal_first, block_part_diagonal_second]
private theorem comp_blockEntries_eq (g : M2 n) (j : ℕ) (T : Matrix (blkA (n := n) j) (blkA j) ℂ)
    (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    g * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1 =
      g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0
        (embOn (blkA j) T + embOn (blkB j) S) := by
  have h := g_mX g 0 (embOn (blkA j) T) (embOn (blkB j) S) 0
  simp only [add_zero] at h
  rw [h, conjL_apply]
  simp only [ContinuousLinearMap.zero_apply, block_part_linear_apply, block_part_embedding_first, block_part_embedding_second]
end PositivityTheory.Rg.Sw.LVs.TC
namespace PositivityTheory.Rg.Sw.LVs
end PositivityTheory.Rg.Sw.LVs
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
set_option maxHeartbeats 800000
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution (hA : IterAffine) (hB : DetDBlock) : TopComp := by
  intro n j F Ω hΩ hG hF hinv hhyp g hg
  have hgΩ : g ∈ Ω := hG hg
  have hc : (2 * Complex.I)⁻¹ ≠ 0 := by simp [Complex.I_ne_zero]
  have hLc : Continuous fun t : Matrix (Fin n) (Fin n) ℂ =>
      g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t :=
    continuous_const.add (ContinuousLinearMap.continuous _)
  have hΩ' : IsOpen ((fun t : Matrix (Fin n) (Fin n) ℂ =>
      g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t) ⁻¹' Ω) := hΩ.preimage hLc
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ (fun t : Matrix (Fin n) (Fin n) ℂ =>
      g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t) ⁻¹' Ω := by
    simp only [Set.mem_preimage, map_zero, add_zero]
    exact hgΩ
  have hψ : ContDiffOn ℂ ∞ (fun t : Matrix (Fin n) (Fin n) ℂ =>
      F (g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t))
      ((fun t : Matrix (Fin n) (Fin n) ℂ =>
        g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t) ⁻¹' Ω) :=
    hF.comp (contDiff_const.add (ContinuousLinearMap.contDiff _)).contDiffOn (fun t ht => ht)
  have hmain := hB n j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) _ _ hΩ' h0 hψ
  have hzero : (detD fun t : Matrix (Fin n) (Fin n) ℂ =>
      F (g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0
        (bdiag j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t))) = 0 := by
    refine Eq.trans ?_ (top_zero (j := j) hA hΩ hG hF hhyp hg)
    have hev : (fun t : Matrix (Fin n) (Fin n) ℂ =>
        F (g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0
          (bdiag j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t))) =ᶠ[𝓝 0]
        fun t => F (g + topL g j t) := by
      have e1 : ∀ᶠ t in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), g + topL g j t ∈ Ω :=
        (continuous_const.add (topL g j).continuous).continuousAt.preimage_mem_nhds
          (by simpa using hΩ.mem_nhds hgΩ)
      have hc2 : Continuous fun t : Matrix (Fin n) (Fin n) ℂ => g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j))
          (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 (bdL j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t) :=
        continuous_const.add ((ContinuousLinearMap.continuous _).comp (ContinuousLinearMap.continuous _))
      have e2 : ∀ᶠ t in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j))
          (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 (bdL j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t) ∈ Ω := by
        have hm : Ω ∈ 𝓝 (g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j))
            (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 (bdL j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) 0)) := by
          rw [map_zero, map_zero, add_zero]
          exact hΩ.mem_nhds hgΩ
        exact hc2.continuousAt.preimage_mem_nhds hm
      filter_upwards [e1, e2] with t ht1 ht2
      rw [bdL_apply, conjL_bdiag_eq_mul_mX_blockEntries] at ht2
      rw [eq_mul_mX_mul_mX_blockEntries] at ht1
      rw [conjL_bdiag_eq_mul_mX_blockEntries, eq_mul_mX_mul_mX_blockEntries]
      exact (hinv _ _ _ ht1 ht2 (supp_smul _ _) (supp_smul _ _)).symm
    have hI := (hev.iteratedFDeriv ℂ (Fintype.card (Fin n))).eq_of_nhds
    unfold detD
    rw [hI]
  rw [hzero] at hmain
  have hX := (mul_eq_zero.mp hmain.symm).resolve_left
    (mul_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ (neg_ne_zero.mpr hc)))
  simpa only [comp_blockEntries_eq] using hX
end PositivityTheory.Rg.Sw.LVs.TC
