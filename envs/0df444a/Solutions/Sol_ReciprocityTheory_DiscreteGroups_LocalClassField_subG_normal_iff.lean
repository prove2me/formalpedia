-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.subG_normal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:42.178019+00:00
-- url     : https://prove2.me/submissions/2a2cd538-f91a-4dd8-bfc2-f98a49e710f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_iff_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (h : K ≤ L) : (subG p K L).Normal ↔ ∀ (σ : GK p K), ∀ x ∈ L, σ x ∈ L := by
  refine ⟨fun hn σ x hx => ?_, subG_normal_of_stable⟩
  rw [mem_iff_fixed h]
  intro τ hτ
  have h1 : (σ⁻¹ * τ * σ⁻¹⁻¹) x = x := hn.conj_mem τ hτ σ⁻¹ x hx
  rw [inv_inv] at h1
  have h2 : σ ((σ⁻¹ * τ * σ) x) = τ (σ x) := by
    show (σ * (σ⁻¹ * τ * σ)) x = (τ * σ) x
    rw [mul_assoc, mul_inv_cancel_left]
  rw [← h2, h1]
end ReciprocityTheory.DiscreteGroups.LocalClassField
