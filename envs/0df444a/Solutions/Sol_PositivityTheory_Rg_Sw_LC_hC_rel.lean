-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.hC_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:46:24.978021+00:00
-- url     : https://prove2.me/submissions/5a8aac58-57a9-42cd-8952-0399a276584b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_GaussianMomentRecurrence
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContrEqOfSubset
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_flip_flip
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LC.flip_flip



set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution (c : ℝ) (p q : ℕ) : hC c (p + 1) q = (2 * c : ℂ) * (q : ℂ) * hC c p (q - 1) := by
  rcases q with _ | q
  · simp [hC]
  · simp only [hC, Nat.add_sub_cancel, Nat.add_right_cancel_iff]
    split_ifs with h
    · subst h; rw [Nat.factorial_succ]; push_cast; ring
    · simp
end PositivityTheory.Rg.Sw.LC
