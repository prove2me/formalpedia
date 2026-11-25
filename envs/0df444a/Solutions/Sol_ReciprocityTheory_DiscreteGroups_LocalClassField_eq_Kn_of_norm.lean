-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.eq_Kn_of_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:37:55.89687+00:00
-- url     : https://prove2.me/submissions/7b6c6e67-e530-4197-b9c5-16e9b0b38d0f

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_le_of_resK_le_of_norm
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kn_le_of_qK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_finite_resK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_resK_mono
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finiteDimensional_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finite_resK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finrank_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_qK_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_qK_le_pow_finrank
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_resK_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hKL : K ≤ L) {n : ℕ} (hn : 0 < n)
    (hdeg : Module.finrank ℚ_[p] L = n * Module.finrank ℚ_[p] K)
    (h : ∀ x ∈ L, ∃ y ∈ K, ‖x‖ = ‖y‖) : L = Kn p K n := by
  have hd : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
  have hL : FiniteDimensional ℚ_[p] L :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact Nat.mul_pos hn hd)
  obtain ⟨f, hf, hq, -⟩ := qK_le_pow_finrank p K hK hL hKL
  have hM : FiniteDimensional ℚ_[p] (Kn p K f) := finiteDimensional_Kn p K hK hf
  have hML : Kn p K f ≤ L := Kn_le_of_qK p K hK hL hKL (n := f) (m := 1) (by rw [mul_one]; exact hq)
  have hres : resK p L ≤ resK p (Kn p K f) := by
    have hfin : Finite (resK p L) := finite_resK p L hL
    have hsub : (resK p (Kn p K f) : Set (kbar p)) ⊆ (resK p L : Set (kbar p)) := resK_mono p hML
    have hcard : (resK p L : Set (kbar p)).ncard ≤ (resK p (Kn p K f) : Set (kbar p)).ncard := by
      have e1 : (resK p L : Set (kbar p)).ncard = qK p L := (Nat.card_coe_set_eq _).symm
      have e2 : (resK p (Kn p K f) : Set (kbar p)).ncard = qK p (Kn p K f) :=
        (Nat.card_coe_set_eq _).symm
      rw [e1, e2, hq, qK_Kn p K hK hf]
    have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
    intro c hc
    have : c ∈ (resK p (Kn p K f) : Set (kbar p)) := by rw [heq]; exact hc
    exact this
  have hLM : L = Kn p K f :=
    le_antisymm (le_of_resK_le_of_norm p hM hML hres
      (fun x hx => by
        obtain ⟨y, hy, hxy⟩ := h x hx
        exact ⟨y, le_Kn p K f hy, hxy⟩)) hML
  have hfn : f = n := by
    have h1 := finrank_Kn p K hK hf
    rw [← hLM, hdeg] at h1
    exact (Nat.eq_of_mul_eq_mul_right hd h1).symm
  rw [hLM, hfn]
end ReciprocityTheory.DiscreteGroups.LocalClassField
