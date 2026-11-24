-- Prove2me | solution 1 for P2M_systemOfUnits_existence__26f57ceed3f9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:44:14.144515+00:00
-- url     : https://prove2.me/submissions/6942cc63-8940-4243-8b78-9942534af152

module
public import Definitions.Def_FltRegular_NumberTheory_CyclotomicRing
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Theorems.Thm_systemOfUnits_ex_not_mem
public import Theorems.Thm_CyclotomicIntegers_exists_dvd_int


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
theorem _root_.solution [Module A G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < s) :
    Nonempty (systemOfUnits p G (R + 1)) := by
  obtain ⟨g, hg⟩ := ex_not_mem p hp G s hf S hR
  refine ⟨⟨Fin.cases g S.units, ?_⟩⟩
  refine LinearIndependent.finCons' g S.units S.linearIndependent (fun a y hy ↦ ?_)
  by_contra! ha
  have := Fact.mk hp
  obtain ⟨n, h0, f, Hf⟩ := CyclotomicIntegers.exists_dvd_int p _ ha.2
  have hy' := congr_arg (f • ·) ha.1
  rw [smul_zero, smul_add, smul_smul, mul_comm f,
    ← Hf, ← eq_neg_iff_add_eq_zero, Int.cast_smul_eq_zsmul] at hy'
  apply hg _ h0
  rw [hy']
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hy)
end systemOfUnits
