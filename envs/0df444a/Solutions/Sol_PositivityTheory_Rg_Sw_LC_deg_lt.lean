-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.deg_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:46.627271+00:00
-- url     : https://prove2.me/submissions/bbd74b9d-fd2e-43a0-947f-de0d63c50d11

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContrEqOfSubset
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableRpowGauss
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FockMomOfBasic
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
theorem _root_.solution (s : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) (hk : s k ≠ 0)
    (t : Fin m × Fin n × Bool →₀ ℕ) (ht : ∀ x, t x ≤ (s - Finsupp.single k 1 : Fin m × Fin n × Bool →₀ ℕ) x) : ∑ x, t x < ∑ x, s x := by
  refine lt_of_le_of_lt (Finset.sum_le_sum fun x _ => ht x) ?_
  refine Finset.sum_lt_sum (fun x _ => by simp) ⟨k, Finset.mem_univ _, ?_⟩
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
  omega
end PositivityTheory.Rg.Sw.LC
