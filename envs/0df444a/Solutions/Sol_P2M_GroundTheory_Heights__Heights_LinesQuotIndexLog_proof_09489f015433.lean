-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesQuotIndexLog_proof_09489f015433
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:24.762198+00:00
-- url     : https://prove2.me/submissions/1a606ef2-e636-4fc5-b758-de0181383afe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotIndexLog

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
open NumberField Matrix
namespace GroundTheory.Heights₂.Heights
namespace LinesQuotIndexLog
theorem _root_.solution (h1 : LinesQuotIndexSplit.Statement)
    (h2 : LinesProjIndexLower.Statement) (h3 : LinesIdealIndexPos.Statement)
    (h4 : LinesProductFormula.Statement) (h5 : LinesCoordDet.Statement) :
    LinesQuotIndexLog.Statement := by
  intro K _ _ n m k a B b c τ ha hBl hBr hτ hli
  have hsplit := h1 K n m k a B b c τ ha hBl hBr hτ hli
  have hlow := h2 K n m k a B τ ha hBr hτ
  have hpos : 0 < ∏ j, idealIndex (a (τ j)) :=
    Finset.prod_pos fun j _ => h3 K (a (τ j)) (ha (τ j))
  have hdet := (h5 K n m k B b c hBl hli).2
  have hN : Algebra.norm ℚ (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hdet
  have hpf := h4 K _ hdet
  have hGpos := lt_of_lt_of_le hpos hlow
  have hNabs : |((Algebra.norm ℚ (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det : ℚ) : ℝ)| ≠ 0 :=
    abs_ne_zero.mpr (Rat.cast_ne_zero.mpr hN)
  rw [hsplit, Real.log_mul hGpos.ne' hNabs, hpf,
    ← Real.log_prod fun j _ => (h3 K (a (τ j)) (ha (τ j))).ne']
  exact add_le_add (Real.log_le_log hpos hlow) le_rfl
end LinesQuotIndexLog
end GroundTheory.Heights₂.Heights
