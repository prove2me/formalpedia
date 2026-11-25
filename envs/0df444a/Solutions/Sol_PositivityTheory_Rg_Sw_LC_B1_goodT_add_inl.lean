-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.goodT_add_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:41:40.684502+00:00
-- url     : https://prove2.me/submissions/dc7209d6-4e0a-4d80-b782-f90ac67dc210

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
variable (ε : Fin m → Bool)
namespace PositivityTheory.Rg.Sw.LC.B1
theorem _root_.solution (t : σ ⊕ σ →₀ ℕ) (μ : σ →₀ ℕ) (ht : GoodT ε t) (hμ : ∀ k ∈ μ.support, inF1 ε k) :
    GoodT ε (Finsupp.mapDomain Sum.inl μ + t) := by
  intro k hk
  simp only [Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inl_injective] at hk
  have h2 : (Finsupp.mapDomain Sum.inl μ : σ ⊕ σ →₀ ℕ) (Sum.inr k) = 0 := by
    rw [Finsupp.mapDomain_of_notMem_range]; rintro ⟨x, hx⟩; exact Sum.inl_ne_inr hx
  rw [h2, zero_add] at hk
  by_cases hμk : μ k = 0
  · rw [hμk, zero_add] at hk; exact ht k hk
  · exact hμ k (Finsupp.mem_support_iff.mpr hμk)
end PositivityTheory.Rg.Sw.LC.B1
