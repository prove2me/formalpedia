-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.G.bf_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:41:10.431801+00:00
-- url     : https://prove2.me/submissions/b21a9f1e-7f9d-455a-8006-3f643f2534ff

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_bf_add_right

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
namespace PositivityTheory.Rg.Sw.LC.CoreC.G
theorem _root_.solution (w : (τ →₀ ℕ) → ℂ) {ι : Type} (I : Finset ι) (p : MvPolynomial τ ℂ) (f : ι → MvPolynomial τ ℂ) :
    bf w p (∑ i ∈ I, f i) = ∑ i ∈ I, bf w p (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [bf]
  | insert a I ha ih => rw [Finset.sum_insert ha, bf_add_right, ih, Finset.sum_insert ha]
end PositivityTheory.Rg.Sw.LC.CoreC.G
