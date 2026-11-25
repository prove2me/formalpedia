-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.contr_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:59:48.758861+00:00
-- url     : https://prove2.me/submissions/4f31eeb4-1962-49dc-959a-132ca2d9e518

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_GaussianMomentRecurrence
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContrEqOfSubset
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_contr_eq_of_subset

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
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution (c : ℝ) (p q : PX m n) : contr c (p + q) = contr c p + contr c q := by
  classical
  rw [contr_eq_of_subset c (p + q) (p.support ∪ q.support) support_add,
    contr_eq_of_subset c p (p.support ∪ q.support) Finset.subset_union_left,
    contr_eq_of_subset c q (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_add, add_mul]
end PositivityTheory.Rg.Sw.LC
