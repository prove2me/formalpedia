-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Core.fform_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:41:01.304196+00:00
-- url     : https://prove2.me/submissions/f33bad21-3416-475c-bbb7-e17d915e36be

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_EquivLift
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FformSmulRight
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_fform_eq_sum

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Core
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Core
theorem _root_.solution (c : ℝ) (p q : PX m n) (r : ℂ) : fform c p (r • q) = r * fform c p q := by
  classical
  rw [fform_eq_sum c p (r • q) (p.support ∪ q.support) (Finset.union_subset Finset.subset_union_left
      (support_smul.trans Finset.subset_union_right)),
    fform_eq_sum c p q (p.support ∪ q.support) le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_smul, smul_eq_mul]; ring
end PositivityTheory.Rg.Sw.LC.Core
