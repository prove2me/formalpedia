-- Prove2me | solution 1 for SPP.nonwitnessGroup_of_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:13:24.288906+00:00
-- url     : https://prove2.me/submissions/f5a756d7-971f-40a4-8ef5-df8ebd7611d8

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_SPP_orderOf_dvd_sub_one
import Theorems.Thm_SPP_mem_nonwitnessGroup
import Theorems.Thm_SPP_nonwitnessGroup_le
import Theorems.Thm_SPP_of_prime_pow_of_fpp
import Theorems.Thm_FPP_orderOf_dvd_sub_one
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
import Theorems.Thm_Subgroup_mem_closure_neg_one
import Theorems.Thm_ZMod_fst_chineseRemainder
import Theorems.Thm_ZMod_snd_chineseRemainder
import Theorems.Thm_ZMod_unitsMap_neg
attribute [local simp] P2M_ZMod_fst_chineseRemainder__e38dff19d888
attribute [local simp] P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
attribute [local simp] Subgroup.mem_closure_neg_one
attribute [local simp] ZMod.fst_chineseRemainder
attribute [local simp] ZMod.snd_chineseRemainder
attribute [local simp] ZMod.unitsMap_neg



set_option autoImplicit false
open Nat
open SPP
open Subgroup
variable {n : ℕ}
variable {m p : ℕ} [pp : Fact p.Prime]
namespace SPP
theorem _root_.solution (hm : 0 < m) (hp : 2 < p) :
    nonwitnessGroup (p ^ m) = (powMonoidHom (p - 1)).ker := by
  have ⟨k, hk⟩ : p - 1 ∣ p ^ m - 1 := by
    clear hm
    induction m with
    | zero => simp
    | succ k ih =>
      have h1 : (p ^ k - 1) * p + (p - 1) = p ^ (k + 1) - 1 := by
        rw [Nat.sub_mul, Nat.one_mul, ← Nat.add_sub_assoc (by omega : 1 ≤ p),
          Nat.sub_add_cancel (Nat.le_mul_of_pos_left p (Nat.pos_of_ne_zero (pow_ne_zero k pp.out.ne_zero))),
          ← Nat.pow_succ]
      rw [← h1]
      exact dvd_add (dvd_mul_of_dvd_left ih p) (dvd_refl _)
  apply le_antisymm
  · apply nonwitnessGroup_le
    intro a ha
    have : Nat.gcd (φ (p ^ m)) (p ^ m - 1) = p - 1 := by
      rw [totient_prime_pow pp.out hm, Nat.gcd_comm, Coprime.gcd_mul _ <| .pow_left _ <|
        (coprime_self_sub_right (one_le_two.trans pp.out.two_le)).mpr <| coprime_one_right _,
        Coprime.gcd_eq_one <| .pow_right _ <| (coprime_pow_right_iff hm _ _).mp <|
        (coprime_self_sub_left (one_le_pow _ _ pp.out.pos)).mpr <| coprime_one_left _, one_mul,
        gcd_eq_right ⟨k, hk⟩]
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← orderOf_dvd_iff_pow_eq_one, ← this]
    apply Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (ZMod.pow_totient a))
    rw [← orderOf_units]
    exact orderOf_dvd_sub_one ha
  · intro a ha
    rw [MonoidHom.mem_ker, powMonoidHom_apply, Units.ext_iff] at ha
    push_cast at ha
    exact mem_nonwitnessGroup (of_prime_pow_of_fpp hm hp (by rw [FPP, hk, pow_mul, ha, one_pow]))
end SPP
