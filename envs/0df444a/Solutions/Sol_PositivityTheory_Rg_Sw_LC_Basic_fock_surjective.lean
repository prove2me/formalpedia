-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.fock_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:35:24.685824+00:00
-- url     : https://prove2.me/submissions/a9c58c9b-0333-4972-a04e-6244c1a18d83

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_surj_deg

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Basic
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Basic
theorem _root_.solution (c : ℝ) (hc : 0 < c) : Function.Surjective (fock (m := m) (n := n) c) := by
  intro Q
  refine fock_surj_deg c hc (Q.support.sup Finsupp.degree + 1) Q fun t ht => ?_
  exact Nat.lt_succ_of_le (Finset.le_sup ht)
end PositivityTheory.Rg.Sw.LC.Basic
