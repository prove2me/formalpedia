-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.pos_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:17:45.855351+00:00
-- url     : https://prove2.me/submissions/efee35a3-b2c9-4cc5-b827-db40edd83006

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_continuousOn_wM
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_continuous_minorOn
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_wM_one
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_second_cayley_block_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (j : ℕ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g) :
    0 < ∫ k, ‖minorOn (blkA j) (wM (ι k))‖ ^ 2 * ‖minorOn (blkB j) (wM (ι k))‖ ^ 2 ∂μ := by
  have hw : Continuous (fun k => wM (ι k)) :=
    continuousOn_wM.comp_continuous hι fun k => by
      obtain ⟨g, hg⟩ : InK (ι k) := (hK (ι k)).2 ⟨k, rfl⟩
      exact det_second_cayley_block_ne_zero g
  have hc : Continuous (fun k => ‖minorOn (blkA j) (wM (ι k))‖ ^ 2 * ‖minorOn (blkB j) (wM (ι k))‖ ^ 2) :=
    (((continuous_minorOn _).comp hw).norm.pow 2).mul (((continuous_minorOn _).comp hw).norm.pow 2)
  have hm1 : ∀ s : Finset (Fin n), minorOn s (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := fun s => by
    rw [minorOn]
    have : (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n)) = 1 := by
      ext a b
      by_cases h : a = b
      · subst h; simp
      · have h' : (a : Fin n) ≠ b := fun e => h (Subtype.ext e)
        rw [Matrix.submatrix_apply, Matrix.one_apply_ne h', Matrix.one_apply_ne h]
    rw [this, det_one]
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
    (fun k => by positivity) (x := 1) ?_
  rw [map_one, wM_one, hm1, hm1]; norm_num
end PositivityTheory.Rg.Sw.LVs
