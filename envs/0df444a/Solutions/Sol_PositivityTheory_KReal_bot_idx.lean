-- Prove2me | solution 1 for PositivityTheory.KReal.bot_idx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:39.685784+00:00
-- url     : https://prove2.me/submissions/91bc5078-0394-43f7-9fdc-31e6d6997f98

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreComb

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
namespace PositivityTheory.KReal
theorem _root_.solution {N : ℕ} (f g : Fin N → ℚ) (j : Fin N) (hdom : ∀ j', j < j' → g j' ≤ g j)
    (hg : g j = f j - 1) (hg' : ∀ j', j' ≠ j → g j' = f j') (hf : ∀ j', j < j' → f j' = f j) :
    (j : ℕ) + 1 = N := by
  by_contra hne
  have hlt : (j : ℕ) + 1 < N := by
    have := j.isLt
    omega
  have h0 : j < (⟨(j : ℕ) + 1, hlt⟩ : Fin N) := by
    rw [Fin.lt_def]
    exact Nat.lt_succ_self _
  have e1 := hdom _ h0
  have e2 := hg' ⟨(j : ℕ) + 1, hlt⟩ (ne_of_gt h0)
  have e3 := hf _ h0
  linarith
end PositivityTheory.KReal
