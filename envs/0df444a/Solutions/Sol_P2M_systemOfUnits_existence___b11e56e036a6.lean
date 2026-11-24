-- Prove2me | solution 1 for P2M_systemOfUnits_existence___b11e56e036a6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:02.01966+00:00
-- url     : https://prove2.me/submissions/76b92258-4fdb-400f-8c6a-a5d10ca5bc9d

module
public import Definitions.Def_FltRegular_NumberTheory_CyclotomicRing
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Theorems.Thm_systemOfUnits_existence0
public import Theorems.Thm_P2M_systemOfUnits_existence__26f57ceed3f9

set_option autoImplicit false
@[expose] public section
public section
open FiniteDimensional
open NumberField
variable (p : ℕ) (hp : Nat.Prime p)
open Module Finset
variable (G : Type*) [AddCommGroup G] (s : ℕ) (hf : finrank ℤ G = s * (p - 1))
local notation "A" => (CyclotomicIntegers p)
open systemOfUnits
include hp hf
variable [Module.Free ℤ G]
namespace systemOfUnits
theorem _root_.solution [Module A G] {R : ℕ} (hR : R ≤ s) : Nonempty (systemOfUnits p G R) := by
  induction R with
  | zero => exact existence0 p G
  | succ n ih =>
      obtain ⟨S⟩ := ih (le_trans (Nat.le_succ n) hR)
      exact existence' p hp G s hf S (lt_of_lt_of_le (Nat.lt_add_one n) hR)
end systemOfUnits
