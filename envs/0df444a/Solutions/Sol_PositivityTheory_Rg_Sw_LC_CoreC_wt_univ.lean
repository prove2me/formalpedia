-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.wt_univ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:10.351444+00:00
-- url     : https://prove2.me/submissions/0dd2bf99-83ed-49a6-93ed-bc3008451831

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    wt c s = ∏ k, ((s k).factorial : ℝ) * (2 * c) ^ (s k) := by
  unfold wt
  refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
  have : s k = 0 := by simpa [Finsupp.mem_support_iff] using hk
  simp [this]
end PositivityTheory.Rg.Sw.LC.CoreC
