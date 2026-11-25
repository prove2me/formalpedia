-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms.pev_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:32:55.96808+00:00
-- url     : https://prove2.me/submissions/8820e830-48fb-45a3-af08-6b913345e5ba

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PNoLogOde
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_NoLogarithmTerms_pev_eq

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
theorem _root_.solution (c : ℂ) (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev (C c * p) f t = c * pev p f t := by
  simp only [pev_eq, Polynomial.C_mul', map_smul, smul_eq_mul]
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms
