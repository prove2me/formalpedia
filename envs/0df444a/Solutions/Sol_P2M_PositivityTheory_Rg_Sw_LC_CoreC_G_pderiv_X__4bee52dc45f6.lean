-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LC_CoreC_G_pderiv_X__4bee52dc45f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:42.397286+00:00
-- url     : https://prove2.me/submissions/2b20a747-608b-41ad-9bbb-a7a6d4d3e0af

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreC PositivityTheory.Rg.Sw.LC.CoreC.G
variable {τ : Type} [Fintype τ] [DecidableEq τ]
variable (w : (τ →₀ ℕ) → ℂ)
variable {w} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
include hw
omit hw
omit [Fintype τ]
namespace PositivityTheory.Rg.Sw.LC.CoreC.G
theorem _root_.solution (v u : τ) : pderiv v (X u : MvPolynomial τ ℂ) = if v = u then 1 else 0 := by
  rw [pderiv_X]; by_cases h : v = u
  · subst h; simp
  · simp [Pi.single_apply, Ne.symm h, h]
end PositivityTheory.Rg.Sw.LC.CoreC.G
