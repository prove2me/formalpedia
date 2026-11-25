-- Prove2me | solution 1 for PositivityTheory.ThK.SiegelT.box_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:58:02.445274+00:00
-- url     : https://prove2.me/submissions/da75deab-f50b-47e3-ab92-1934e54df59e

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAn
import Theorems.Thm_PositivityTheory_ThK_SiegelT_cont_elim
import Theorems.Thm_PositivityTheory_ThK_SiegelT_cont_inl
import Theorems.Thm_PositivityTheory_ThK_SiegelT_cont_inr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SiegelT
open Matrix GlobalTheory.WeilM Topology Filter
variable {R : Type} [TopologicalSpace R] [T2Space R] {κ κ' : Type}
namespace PositivityTheory.ThK.SiegelT
theorem _root_.solution {φ₁ : (κ → R) → ℂ} {φ₂ : (κ' → R) → ℂ} (h₁ : φ₁ ∈ SB (κ → R)) (h₂ : φ₂ ∈ SB (κ' → R)) :
    (fun x : κ ⊕ κ' → R => φ₁ (x ∘ Sum.inl) * φ₂ (x ∘ Sum.inr)) ∈ SB (κ ⊕ κ' → R) := by
  refine ⟨(h₁.1.comp_continuous cont_inl).mul (h₂.1.comp_continuous cont_inr),
    HasCompactSupport.intro ((h₁.2.isCompact.prod h₂.2.isCompact).image cont_elim) fun x hx => ?_⟩
  by_contra hne
  exact hx ⟨(x ∘ Sum.inl, x ∘ Sum.inr), ⟨subset_tsupport _ (left_ne_zero_of_mul hne),
    subset_tsupport _ (right_ne_zero_of_mul hne)⟩, Sum.elim_comp_inl_inr x⟩
end PositivityTheory.ThK.SiegelT
