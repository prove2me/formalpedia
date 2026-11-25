-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreD.box_le_first_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:32:59.072801+00:00
-- url     : https://prove2.me/submissions/06749cdc-3cd8-4d3c-bce6-7bf8447e4ca0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymKEqZeroOfOm
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BoxLeFirstFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreD
variable {m n : ℕ} {ε : Fin m → Bool}
namespace PositivityTheory.Rg.Sw.LC.CoreD
theorem _root_.solution (R : Set (Fin m → ℕ)) : box (n := n) ε R ≤ F1 ε := by
  refine Submodule.span_le.2 fun p ⟨s, hs, _, hp⟩ => ?_
  subst hp
  change monomial s 1 ∈ MvPolynomial.supported ℂ {k | inF1 ε k}
  rw [MvPolynomial.mem_supported, vars_monomial one_ne_zero]
  exact fun k hk => hs k hk
end PositivityTheory.Rg.Sw.LC.CoreD
