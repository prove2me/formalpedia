-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.comap_inl_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:44:06.742972+00:00
-- url     : https://prove2.me/submissions/2ada22a7-af57-4552-8c4f-14b8a9e3b0bf

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
theorem _root_.solution (t : σ ⊕ σ →₀ ℕ) (μ : σ →₀ ℕ) :
    (t + Finsupp.mapDomain Sum.inl μ).comapDomain Sum.inl Sum.inl_injective.injOn =
      t.comapDomain Sum.inl Sum.inl_injective.injOn + μ := by
  ext k
  simp [Finsupp.comapDomain_apply, Finsupp.mapDomain_apply Sum.inl_injective]
end PositivityTheory.Rg.Sw.LC.B1
