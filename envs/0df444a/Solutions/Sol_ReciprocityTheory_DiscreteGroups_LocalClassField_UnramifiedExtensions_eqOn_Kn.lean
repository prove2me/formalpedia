-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.eqOn_Kn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:35.477877+00:00
-- url     : https://prove2.me/submissions/0891e34c-1d27-425a-a812-2f0d7d2baaa9

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
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
theorem _root_.solution {n : ℕ} {σ τ : GK p K}
    (h : ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → σ ζ = τ ζ) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) :
    σ x = τ x := by
  have h1 : Kn p K n ≤ eqField K σ τ := by
    apply Kn_le
    · intro y hy
      change σ y = τ y
      exact (σ.commutes ⟨y, hy⟩).trans (τ.commutes ⟨y, hy⟩).symm
    · exact h
  exact h1 hx
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
