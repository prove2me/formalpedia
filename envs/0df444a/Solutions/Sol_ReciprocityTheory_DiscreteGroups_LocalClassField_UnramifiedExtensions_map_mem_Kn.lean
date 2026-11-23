-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.map_mem_Kn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:35.435565+00:00
-- url     : https://prove2.me/submissions/2c4b6eaf-6bec-4674-9c9e-c1b8606b55b4

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_Kn_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_Kn_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable (K)
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution (n : ℕ) (σ : GK p K) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) : σ x ∈ Kn p K n := by
  have h : Kn p K n ≤ (Kn p K n).comap ((σ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
      PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) := by
    apply Kn_le
    · intro y hy
      change σ y ∈ Kn p K n
      have : σ y = y := σ.commutes ⟨y, hy⟩
      rw [this]; exact le_Kn K n hy
    · intro ζ hζ
      change σ ζ ∈ Kn p K n
      apply mem_Kn_of_pow
      rw [← map_pow, hζ, map_one]
  exact h hx
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
