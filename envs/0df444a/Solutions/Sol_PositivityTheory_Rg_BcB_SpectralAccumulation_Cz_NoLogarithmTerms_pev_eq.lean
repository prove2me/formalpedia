-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms.pev_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:39.874673+00:00
-- url     : https://prove2.me/submissions/29534a44-8796-4543-98e3-4d6a3c9105e1

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
theorem _root_.solution (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev p f t = pevL f t p := by
  simp only [pev, pevL, Polynomial.lsum_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
  exact congrArg p.sum (funext fun k => funext fun a => mul_comm _ _)
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms
