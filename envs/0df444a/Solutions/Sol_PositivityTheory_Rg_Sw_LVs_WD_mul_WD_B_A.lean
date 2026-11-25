-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.WD_mul_WD_B_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:57:28.025077+00:00
-- url     : https://prove2.me/submissions/58816336-9633-45b3-a8d5-f31166594d2f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_WD_prod
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_embOn_mul_embOn_disj


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
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (j : ℕ) (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ)
    (T' : Matrix (blkA (n := n) j) (blkA j) ℂ) (S' : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    WD (embOn (blkB j) S) (embOn (blkA j) T) * WD (embOn (blkB j) S') (embOn (blkA j) T') = 0 := by
  have h1 : embOn (blkB j) S * embOn (blkA j) T' = 0 :=
    embOn_mul_embOn_disj (fun c hc hc' => by
      simp only [blkB, Finset.mem_compl] at hc
      exact hc hc') S T'
  have h2 : embOn (blkA j) T * embOn (blkB j) S' = 0 :=
    embOn_mul_embOn_disj (fun c hc hc' => by
      simp only [blkB, Finset.mem_compl] at hc'
      exact hc' hc) T S'
  simp only [WD]
  rw [WD_prod, h1, h2]
  simp
end PositivityTheory.Rg.Sw.LVs
