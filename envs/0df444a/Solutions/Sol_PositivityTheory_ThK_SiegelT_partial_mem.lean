-- Prove2me | solution 1 for PositivityTheory.ThK.SiegelT.partial_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:07.402004+00:00
-- url     : https://prove2.me/submissions/a4a2915a-ee67-4361-84c9-48068c98da60

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
theorem _root_.solution {Φ : (κ ⊕ κ' → R) → ℂ} (h : Φ ∈ SB (κ ⊕ κ' → R)) (l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ) :
    (fun y : κ' → R => l fun x => Φ (Sum.elim x y)) ∈ SB (κ' → R) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun y₀ => ?_,
    HasCompactSupport.intro (h.2.isCompact.image cont_inr) fun y hy => ?_⟩
  · have hK := (h.2.isCompact.image (cont_inl (κ := κ) (κ' := κ'))).eventually_forall_of_forall_eventually (x₀ := y₀)
      (P := fun y x => Φ (Sum.elim x y) = Φ (Sum.elim x y₀)) (fun x _ => by
        have a := (h.1.comp_continuous (cont_elim.comp continuous_swap)).eventually_eq (y₀, x)
        have b := (h.1.comp_continuous (cont_elim.comp ((Continuous.prodMk_left y₀).comp
          (continuous_snd (X := κ' → R))))).eventually_eq (y₀, x)
        filter_upwards [a, b] with z ha hb
        exact ha.trans hb.symm)
    filter_upwards [hK] with y hy
    congr 1
    funext x
    by_cases hx : x ∈ (fun z : κ ⊕ κ' → R => z ∘ Sum.inl) '' tsupport Φ
    · exact hy x hx
    · have : ∀ y, Φ (Sum.elim x y) = 0 := fun y => by
        by_contra hne
        exact hx ⟨Sum.elim x y, subset_tsupport _ hne, rfl⟩
      rw [this, this]
  · have : (fun x : κ → R => Φ (Sum.elim x y)) = 0 := funext fun x => by
      by_contra hne
      exact hy ⟨Sum.elim x y, subset_tsupport _ hne, rfl⟩
    rw [this, map_zero]
end PositivityTheory.ThK.SiegelT
