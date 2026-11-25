-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.G.gf_neg_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:41:19.110303+00:00
-- url     : https://prove2.me/submissions/f801d77a-484a-476a-b475-cd5774176977

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_smul_left

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
theorem _root_.solution (p q : MvPolynomial τ ℂ) : gf w (-p) q = -gf w p q := by
  rw [show -p = (-1 : ℂ) • p by simp, gf_smul_left]; simp
end PositivityTheory.Rg.Sw.LC.CoreC.G
