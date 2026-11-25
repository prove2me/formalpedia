-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.sum_ite_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:43:21.240547+00:00
-- url     : https://prove2.me/submissions/51b066c7-7fb8-412c-b919-c7d2014c1a08

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
theorem _root_.solution (g : Fin n → ℂ) (F : Fin n → MvPolynomial (FinalTheorems m n) ℂ) (j0 : Fin n) :
    ∑ x, C (if j0 = x then g x else 0) * F x = C (g j0) * F j0 := by
  rw [Finset.sum_eq_single j0]
  · simp
  · intro x _ hx; rw [if_neg (Ne.symm hx)]; simp
  · intro h; exact absurd (Finset.mem_univ _) h
end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
