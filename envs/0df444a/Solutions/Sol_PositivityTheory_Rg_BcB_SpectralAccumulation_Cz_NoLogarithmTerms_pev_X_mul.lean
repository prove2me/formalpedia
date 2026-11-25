-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms.pev_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:00.573804+00:00
-- url     : https://prove2.me/submissions/6e347d61-355c-42fe-b77e-8bef3e6f4e1f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PNoLogOde
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_NoLogarithmTerms_pev_add
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_NoLogarithmTerms_pev_monomial

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
theorem _root_.solution (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev (X * p) f t = pev p (fun k => f (k + 1)) t := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, pev_add, pev_add, hp, hq]
  | monomial n a => rw [Polynomial.X_mul_monomial, pev_monomial, pev_monomial]
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms
