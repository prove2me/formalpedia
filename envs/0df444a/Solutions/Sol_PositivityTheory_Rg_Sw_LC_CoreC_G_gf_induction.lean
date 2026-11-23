-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.G.gf_induction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:35.432806+00:00
-- url     : https://prove2.me/submissions/f090b9d2-7468-4880-b831-756ccd809cbb

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
namespace PositivityTheory.Rg.Sw.LC.CoreC.G
theorem _root_.solution {P : MvPolynomial τ ℂ → MvPolynomial τ ℂ → Prop}
    (hm : ∀ s t (a b : ℂ), P (monomial s a) (monomial t b))
    (hl : ∀ p p' q, P p q → P p' q → P (p + p') q) (hr : ∀ p q q', P p q → P p q' → P p (q + q')) :
    ∀ p q, P p q := by
  intro p q
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    induction q using MvPolynomial.induction_on' with
    | monomial t b => exact hm s t a b
    | add q q' h1 h2 => exact hr _ _ _ h1 h2
  | add p p' h1 h2 => exact hl _ _ _ h1 h2
end PositivityTheory.Rg.Sw.LC.CoreC.G
