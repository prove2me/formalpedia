-- Prove2me | solution 1 for PositivityTheory.KReal.top_idx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:54:33.320379+00:00
-- url     : https://prove2.me/submissions/5f1080bd-3bd4-41ec-830d-744c6942b51b

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
theorem _root_.solution {N : ℕ} (f g : Fin N → ℚ) (i : Fin N) (hdom : ∀ i', i' < i → g i ≤ g i')
    (hg : g i = f i + 1) (hg' : ∀ i', i' ≠ i → g i' = f i') (hf : ∀ i', i' < i → f i' = f i) :
    (i : ℕ) = 0 := by
  by_contra hne
  have hpos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hne
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have h0 : (⟨0, hN⟩ : Fin N) < i := by
    rw [Fin.lt_def]
    exact hpos
  have e1 := hdom _ h0
  have e2 := hg' ⟨0, hN⟩ (ne_of_lt h0)
  have e3 := hf _ h0
  linarith
end PositivityTheory.KReal
