-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.list_single_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:40:40.088872+00:00
-- url     : https://prove2.me/submissions/11544a1f-9d8b-4c1c-b11d-a6beaeeccd7a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B1
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
local notation "σ" => Fin m × Fin n × Bool
namespace PositivityTheory.Rg.Sw.LC.B1
theorem _root_.solution (γ : σ → ℕ) (l : List σ) (k : σ) (hk : k ∉ l) :
    (l.map fun k => Finsupp.single k (γ k)).sum k = 0 := by
  induction l with
  | nil => simp
  | cons k' l' ih =>
    rw [List.mem_cons, not_or] at hk
    simp only [List.map_cons, List.sum_cons, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
      if_neg (Ne.symm hk.1), zero_add]
    exact ih hk.2
end PositivityTheory.Rg.Sw.LC.B1
