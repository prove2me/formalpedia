-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.sf_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:40:54.190884+00:00
-- url     : https://prove2.me/submissions/4801cb65-e05a-4abc-ae00-2f6821a41344

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_monomial

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
theorem _root_.solution (γ : σ →₀ ℕ) (hγ : ∀ k ∈ γ.support, inF1 ε k) (c : ℂ) :
    SymbolInFirstFamily ε (monomial (Finsupp.mapDomain Sum.inr γ) c : Sym m n) := by
  refine sf_monomial ε _ _ fun k hk => ?_
  have h1 : (Finsupp.mapDomain Sum.inr γ : σ ⊕ σ →₀ ℕ) (Sum.inl k) = 0 := by
    rw [Finsupp.mapDomain_of_notMem_range]; rintro ⟨x, hx⟩; exact Sum.inr_ne_inl hx
  rw [h1, Finsupp.mapDomain_apply Sum.inr_injective] at hk
  exact hγ k (Finsupp.mem_support_iff.mpr (hk.resolve_left (by simp)))
end PositivityTheory.Rg.Sw.LC.B1
