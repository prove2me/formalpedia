-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.G.gf_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:41:16.763558+00:00
-- url     : https://prove2.me/submissions/b705f011-a106-45f0-99ea-26ff808aab32

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
variable (w)
namespace PositivityTheory.Rg.Sw.LC.CoreC.G
theorem _root_.solution (hs : ∀ s, star (w s) = w s) (p q : MvPolynomial τ ℂ) : gf w q p = star (gf w p q) := by
  unfold gf
  rw [Finset.union_comm, star_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [star_mul, star_mul, star_star, hs]; ring
end PositivityTheory.Rg.Sw.LC.CoreC.G
