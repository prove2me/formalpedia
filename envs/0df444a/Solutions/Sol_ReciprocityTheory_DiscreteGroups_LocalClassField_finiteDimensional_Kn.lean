-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:21.435045+00:00
-- url     : https://prove2.me/submissions/3148202b-bf65-4a9f-8ae9-097e5f8b8219

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_not_dvd_qK_pow_sub_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Polynomial
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    FiniteDimensional ℚ_[p] (Kn p K n) := by
  have hnd := UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK hn
  have hm0 : 0 < qK p K ^ n - 1 := Nat.pos_of_ne_zero (by rintro h; exact hnd (h ▸ dvd_zero p))
  have hfin : Finite {ζ : PadicAlgCl p | ζ ^ (qK p K ^ n - 1) = 1} := by
    have : {ζ : PadicAlgCl p | ζ ^ (qK p K ^ n - 1) = 1} =
        (nthRootsFinset (qK p K ^ n - 1) (1 : PadicAlgCl p) : Set (PadicAlgCl p)) := by
      ext ζ
      simp [mem_nthRootsFinset hm0]
    rw [this]
    exact Finset.finite_toSet _
  have h2 : FiniteDimensional ℚ_[p]
      (IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (qK p K ^ n - 1) = 1}) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  exact IntermediateField.finiteDimensional_sup _ _
end ReciprocityTheory.DiscreteGroups.LocalClassField
