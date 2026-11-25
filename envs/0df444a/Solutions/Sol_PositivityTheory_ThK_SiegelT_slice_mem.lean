-- Prove2me | solution 1 for PositivityTheory.ThK.SiegelT.slice_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:10.191888+00:00
-- url     : https://prove2.me/submissions/b06ef3a6-51ed-4e79-81fa-e50ae67bb034

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAn
import Theorems.Thm_PositivityTheory_ThK_SiegelT_cont_elim
import Theorems.Thm_PositivityTheory_ThK_SiegelT_cont_inl

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
theorem _root_.solution {Φ : (κ ⊕ κ' → R) → ℂ} (h : Φ ∈ SB (κ ⊕ κ' → R)) (y : κ' → R) :
    (fun x : κ → R => Φ (Sum.elim x y)) ∈ SB (κ → R) := by
  refine ⟨h.1.comp_continuous (cont_elim.comp (Continuous.prodMk_left y)),
    HasCompactSupport.intro (h.2.isCompact.image cont_inl) fun x hx => ?_⟩
  by_contra hne
  exact hx ⟨Sum.elim x y, subset_tsupport _ hne, rfl⟩
end PositivityTheory.ThK.SiegelT
