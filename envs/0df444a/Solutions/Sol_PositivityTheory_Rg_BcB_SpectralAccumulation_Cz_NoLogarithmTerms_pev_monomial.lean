-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms.pev_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:41.314859+00:00
-- url     : https://prove2.me/submissions/48f56358-f2d6-47d6-ba44-5e741ebc07b9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PNoLogOde

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms
theorem _root_.solution (n : ℕ) (a : ℂ) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev (monomial n a) f t = a * f n t := by
  simp only [pev]
  exact Polynomial.sum_monomial_index _ _ (by simp)
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms
