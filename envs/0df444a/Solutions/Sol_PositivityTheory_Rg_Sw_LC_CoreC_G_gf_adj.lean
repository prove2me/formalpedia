-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.G.gf_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:57:18.453471+00:00
-- url     : https://prove2.me/submissions/e4294355-7804-4976-bba4-3720fbc75ded

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_X_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_pderiv

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
namespace PositivityTheory.Rg.Sw.LC.CoreC.G
theorem _root_.solution (k l : τ) (p q : MvPolynomial τ ℂ) : gf w (X k * pderiv l p) q = gf w p (X l * pderiv k q) := by
  rw [gf_X_mul κ hw, gf_pderiv κ hw]
end PositivityTheory.Rg.Sw.LC.CoreC.G
