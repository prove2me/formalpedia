-- Prove2me | solution 1 for PositivityTheory.KReal.CasGl.count_cross
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:04:20.0652+00:00
-- url     : https://prove2.me/submissions/d11b35af-8baf-49cd-983f-0195c5dd93bf

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCas
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
open PositivityTheory.KReal.CasGl
variable {r s : ℕ}
namespace PositivityTheory.KReal.CasGl
theorem _root_.solution {e f : Ix r s} (h : ¬ sameBlock e f) :
    (∑ a : Ix r s, ∑ b : Ix r s, if sameBlock a b then
      ((if e = a then 1 else 0) + (if f = b then 1 else 0) : ℂ) else 0) = (r : ℂ) + s := by
  rcases e with e | e <;> rcases f with f | f <;> simp [sameBlock] at h ⊢ <;>
    simp [Fintype.sum_sum_type, sameBlock, Finset.sum_add_distrib] <;> ring
end PositivityTheory.KReal.CasGl
