-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.G.bf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:18:16.510686+00:00
-- url     : https://prove2.me/submissions/9b942f72-d289-482c-8d83-568973ccfa77

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
namespace PositivityTheory.Rg.Sw.LC.CoreC.G
theorem _root_.solution (w : (τ →₀ ℕ) → ℂ) (S : Finset (τ →₀ ℕ)) {p q : MvPolynomial τ ℂ} (hp : p.support ⊆ S)
    (hq : q.support ⊆ S) : bf w p q = ∑ s ∈ S, p.coeff s * q.coeff s * w s := by
  unfold bf
  refine Finset.sum_subset (Finset.union_subset hp hq) fun s _ hs => ?_
  simp only [Finset.mem_union, not_or] at hs
  have h0 : p.coeff s = 0 := by
    by_contra h; exact hs.1 (MvPolynomial.mem_support_iff.mpr h)
  simp [h0]
end PositivityTheory.Rg.Sw.LC.CoreC.G
