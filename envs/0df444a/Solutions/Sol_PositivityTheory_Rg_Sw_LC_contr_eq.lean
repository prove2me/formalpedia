-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.contr_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:43.964262+00:00
-- url     : https://prove2.me/submissions/ad2c0266-43b0-4067-a9b6-c11e4ecd605e

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
theorem _root_.solution (c : ℝ) (p : PX m n) : contr c p = ∑ s ∈ p.support, p.coeff s * wC c s := by
  unfold contr wC
  refine Finset.sum_congr rfl fun s _ => ?_
  have : (∏ a, ∏ i, hC c (s (a, i, false)) (s (a, i, true))) =
      if ∀ a i, s (a, i, false) = s (a, i, true) then
        ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false))) else 0 := by
    simp only [hC, Finset.prod_ite_zero, Finset.mem_univ, true_implies]
  rw [this]
  split_ifs <;> simp
end PositivityTheory.Rg.Sw.LC
