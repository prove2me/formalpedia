-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.opMono_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:50.806449+00:00
-- url     : https://prove2.me/submissions/acce396b-09be-4622-b198-f2bd27a40363

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_list_pderiv

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
theorem _root_.solution (γ δ : σ →₀ ℕ) :
    opMono (Finsupp.mapDomain Sum.inr γ) (monomial δ 1 : PX m n) =
      monomial (δ - γ) (∏ k, ((δ k).descFactorial (γ k) : ℂ)) := by
  unfold opMono
  have h0 : ((Finsupp.mapDomain Sum.inr γ : σ ⊕ σ →₀ ℕ)).comapDomain Sum.inl
      (Sum.inl_injective (α := σ) (β := σ)).injOn = (0 : σ →₀ ℕ) := by
    ext k
    rw [Finsupp.comapDomain_apply, Finsupp.mapDomain_of_notMem_range]
    · rfl
    · rintro ⟨x, hx⟩; exact Sum.inr_ne_inl hx
  rw [h0]
  simp only [Finsupp.mapDomain_apply Sum.inr_injective]
  rw [list_pderiv γ _ (Finset.nodup_toList _), Finset.prod_map_toList, Finset.sum_map_toList,
    Finsupp.univ_sum_single]
  rw [← C_apply, C_1, one_mul, one_mul]
end PositivityTheory.Rg.Sw.LC.B1
