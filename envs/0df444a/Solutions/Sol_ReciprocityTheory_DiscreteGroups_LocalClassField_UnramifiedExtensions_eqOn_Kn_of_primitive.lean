-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.eqOn_Kn_of_primitive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:00.781878+00:00
-- url     : https://prove2.me/submissions/402296f7-aa26-4ec0-8dc3-773003c19ddd

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_eqOn_Kn


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
open ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution {n : ℕ} (h0 : qK p K ^ n - 1 ≠ 0) {ζ₀ : PadicAlgCl p}
    (hζ₀ : IsPrimitiveRoot ζ₀ (qK p K ^ n - 1)) {σ τ : GK p K} (h : σ ζ₀ = τ ζ₀) {x : PadicAlgCl p}
    (hx : x ∈ Kn p K n) : σ x = τ x := by
  have : NeZero (qK p K ^ n - 1) := ⟨h0⟩
  refine eqOn_Kn K (fun ζ hζ => ?_) hx
  obtain ⟨k, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
  rw [map_pow, map_pow, h]
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
