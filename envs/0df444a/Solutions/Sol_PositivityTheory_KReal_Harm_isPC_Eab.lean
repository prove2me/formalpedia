-- Prove2me | solution 1 for PositivityTheory.KReal.Harm.isPC_Eab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:56.012116+00:00
-- url     : https://prove2.me/submissions/53a9c0da-c554-4020-bf2a-edf833643e66

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm

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
open PositivityTheory.KReal.Harm
namespace PositivityTheory.KReal.Harm
theorem _root_.solution {m n : ℕ} {a b : Ix m n} (h : ¬ sameBlock a b) : IsPC (Eab a b) := by
  intro x y hxy
  simp only [Eab, Matrix.single_apply]
  split_ifs with hh
  · obtain ⟨rfl, rfl⟩ := hh
    exact absurd hxy h
  · rfl
end PositivityTheory.KReal.Harm
