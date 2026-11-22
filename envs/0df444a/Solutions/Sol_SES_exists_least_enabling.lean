-- Prove2me | solution 1 for SES.exists_least_enabling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:48:48.159926+00:00
-- url     : https://prove2.me/submissions/465fbb8e-47f9-4816-93f8-e74fd16aa1d5

import Definitions.Def_EventStructures_General_Basic
import Definitions.Def_EventStructures_General_Stable
import Theorems.Thm_SES_toFamily_Config
import Theorems.Thm_GES_toFamily_Config
import Theorems.Thm_GES_toFamily_Event
attribute [local simp] GES.toFamily_Config
attribute [local simp] GES.toFamily_Event


attribute [local simp] SES.toFamily_Config

set_option autoImplicit true
open SES
variable {L : Type*} (S : SES L)
local infix:50 " ⊢ " => S.enable
variable {S}
namespace SES
theorem _root_.solution {z : Set S.Event} (hz : S.toGES.isConf z) {e : S.Event}
    {X₀ : Finset S.Event} (hX₀ : X₀ ⊢ e) (hX₀z : ↑X₀ ⊆ z) (hez : e ∈ z) :
    ∃ M : Finset S.Event, (M ⊢ e) ∧ M ⊆ X₀ ∧
      ∀ Y : Finset S.Event, (Y ⊢ e) → ↑Y ⊆ z → M ⊆ Y := by
  classical
  have hmemP : ∀ {W : Finset S.Event},
      W ∈ X₀.powerset.filter (fun W => S.enable W e) ↔ W ⊆ X₀ ∧ (W ⊢ e) := by
    simp [Finset.mem_filter, Finset.mem_powerset]
  obtain ⟨M, hM, hmin⟩ :=
    (X₀.powerset.filter (fun W => S.enable W e)).exists_min_image Finset.card
      ⟨X₀, hmemP.mpr ⟨subset_rfl, hX₀⟩⟩
  obtain ⟨hMX₀, hMen⟩ := hmemP.mp hM
  refine ⟨M, hMen, hMX₀, fun Y hYen hYz => ?_⟩
  have hcons : S.toGES.Consistent (↑M ∪ ↑Y ∪ {e}) :=
    fun W hW => hz.1 W (hW.trans (by
      rintro w ((hw | hw) | hw)
      · exact hX₀z (hMX₀ hw)
      · exact hYz hw
      · exact Set.mem_singleton_iff.mp hw ▸ hez))
  have hen : (M ∩ Y) ⊢ e := S.enable_inter hMen hYen hcons (by simp)
  have hcard := hmin (M ∩ Y) (hmemP.mpr ⟨(Finset.inter_subset_left).trans hMX₀, hen⟩)
  exact (Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcard) ▸
    Finset.inter_subset_right
end SES
