-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.pow_sub_one_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:59:10.369464+00:00
-- url     : https://prove2.me/submissions/697e9ede-ba50-40c9-8592-a539a4671503

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD

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
theorem _root_.solution {q : ℕ} (hq : 1 < q) {n : ℕ} (i : ℕ) :
    q ^ n - 1 ∣ q ^ i - 1 ↔ n ∣ i := by
  constructor
  · intro h
    have h1 := Nat.gcd_eq_left h
    rw [Nat.pow_sub_one_gcd_pow_sub_one] at h1
    have h2 : 1 ≤ q ^ Nat.gcd n i := Nat.one_le_pow _ _ (by omega)
    have h3 : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
    have h4 : q ^ Nat.gcd n i = q ^ n := by omega
    have h5 := Nat.pow_right_injective (show 2 ≤ q by omega) h4
    exact Nat.gcd_eq_left_iff_dvd.1 h5
  · intro h
    exact Nat.pow_sub_one_dvd_pow_sub_one _ h
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
