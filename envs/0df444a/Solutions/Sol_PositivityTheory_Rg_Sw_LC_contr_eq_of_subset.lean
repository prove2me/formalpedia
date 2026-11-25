-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.contr_eq_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:51.928852+00:00
-- url     : https://prove2.me/submissions/729fecfb-8f65-4ab7-a759-85de49ccd7b0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_GaussianMomentRecurrence
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContrEqOfSubset
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_contr_eq

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
theorem _root_.solution (c : ℝ) (p : PX m n) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) (hS : p.support ⊆ S) :
    contr c p = ∑ s ∈ S, p.coeff s * wC c s := by
  rw [contr_eq]
  refine Finset.sum_subset hS fun s _ hs => ?_
  rw [notMem_support_iff.1 hs, zero_mul]
end PositivityTheory.Rg.Sw.LC
