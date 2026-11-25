-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.eq_zero_of_mem_BrKer_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:17:07.836036+00:00
-- url     : https://prove2.me/submissions/677626fb-9f0c-4b1d-a4fd-2dfa36dc65b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfResEqZeroOfCoprime
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfMemBrKerOfCoprime
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_degLK_smul_eq_zero

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
theorem _root_.solution (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : Br p K)
    (hx : x ∈ BrKer h) (k : ℕ) (hk : k • x = 0) (hc : Nat.Coprime k (degLK p K L)) : x = 0 := by
  have h1 := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hk)
    (addOrderOf_dvd_of_nsmul_eq_zero (degLK_smul_eq_zero hL h x hx))
  rw [Nat.Coprime.gcd_eq_one hc, Nat.dvd_one] at h1
  exact AddMonoid.addOrderOf_eq_one_iff.1 h1
end ReciprocityTheory.DiscreteGroups.LocalClassField
