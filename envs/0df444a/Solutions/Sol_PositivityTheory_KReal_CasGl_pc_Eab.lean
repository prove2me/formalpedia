-- Prove2me | solution 1 for PositivityTheory.KReal.CasGl.pc_Eab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:25.448577+00:00
-- url     : https://prove2.me/submissions/7c43ba38-2291-45fe-afd7-f88fce4b5085

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCas
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl
import Theorems.Thm_PositivityTheory_KReal_CasGl_Eab_apply

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
theorem _root_.solution {a b : Ix r s} (h : ¬ sameBlock a b) : IsPC (Eab a b : Mat r s) := by
  intro e f hef
  rw [Eab_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd hef h
  · rfl
end PositivityTheory.KReal.CasGl
