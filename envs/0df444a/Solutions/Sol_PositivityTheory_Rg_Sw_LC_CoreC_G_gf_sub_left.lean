-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.G.gf_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:22.271736+00:00
-- url     : https://prove2.me/submissions/a0b2a527-05fb-4703-82ed-a250228b7389

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_add_left
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_neg_left

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
namespace PositivityTheory.Rg.Sw.LC.CoreC.G
theorem _root_.solution (p p' q : MvPolynomial τ ℂ) : gf w (p - p') q = gf w p q - gf w p' q := by
  rw [sub_eq_add_neg, gf_add_left, gf_neg_left, ← sub_eq_add_neg]
end PositivityTheory.Rg.Sw.LC.CoreC.G
