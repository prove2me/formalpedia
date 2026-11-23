-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreBb.op_eq_sum_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:24.848844+00:00
-- url     : https://prove2.me/submissions/c5f4678a-ebdd-4bc6-9726-86dd3ec71cb7

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreBb
theorem _root_.solution (s : Sym m n) (f : PX m n) (T : Finset ((Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ))
    (hT : s.support ⊆ T) : op s f = ∑ t ∈ T, s.coeff t • opMono t f := by
  unfold op
  refine Finset.sum_subset hT fun t _ ht => ?_
  rw [notMem_support_iff.1 ht, zero_smul]
end PositivityTheory.Rg.Sw.LC.CoreBb
