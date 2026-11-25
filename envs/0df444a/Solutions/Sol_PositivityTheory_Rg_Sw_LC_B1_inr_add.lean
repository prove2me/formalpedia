-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.inr_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:41:43.083089+00:00
-- url     : https://prove2.me/submissions/f7d47a97-4963-43d5-87f6-e4906d83b052

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
theorem _root_.solution (t : σ ⊕ σ →₀ ℕ) (μ : σ →₀ ℕ) (k : σ) :
    ((t + Finsupp.mapDomain Sum.inl μ : σ ⊕ σ →₀ ℕ)) (Sum.inr k) = t (Sum.inr k) := by
  rw [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range, add_zero]
  rintro ⟨x, hx⟩; exact Sum.inl_ne_inr hx
end PositivityTheory.Rg.Sw.LC.B1
