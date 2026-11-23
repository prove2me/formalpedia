-- Prove2me | solution 1 for SPP.G_lt_F_of_not_isPrimePow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:10:45.863803+00:00
-- url     : https://prove2.me/submissions/5657d3c3-9c45-41bf-ab05-20b5a3dbcc41

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_P2M_SPP_s__lt_val__1ca063141b6b
import Theorems.Thm_P2M_SPP_s__spec_e1afc8f96699
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
import Theorems.Thm_P2M_two_pow_val__mul_oddPart_d784ed0aab74
import Theorems.Thm_Subgroup_mem_closure_neg_one
import Theorems.Thm_ZMod_fst_chineseRemainder
import Theorems.Thm_ZMod_snd_chineseRemainder
import Theorems.Thm_ZMod_unitsMap_neg
import Theorems.Thm_exists_pow_prime_dvd_and_coprime_of_odd
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
namespace SPP
theorem _root_.solution [hn : Fact (1 < n)] (ho : Odd n) (hnp : ¬IsPrimePow n) :
    G n < F n := by
  apply lt_of_le_of_ne
  · intro a
    rw [G, mem_comap, powMonoidHom_apply, F, MonoidHom.mem_ker, powMonoidHom_apply,
      mem_closure_neg_one]
    intro ha
    rw [← two_pow_val₂_mul_oddPart (n - 1), ← Nat.sub_add_cancel (s₀_lt_val₂ ho), pow_add,
      mul_assoc, mul_comm, pow_mul, Nat.pow_succ, mul_right_comm, pow_mul]
    rcases ha with ha | ha <;> rw [ha]
    · rw [one_pow, one_pow]
    · rw [neg_one_sq, one_pow]
  · let ⟨p, s, k, _, _, hpsk, cop, hk, hps⟩ :=
      exists_pow_prime_dvd_and_coprime_of_odd hn.out ho hnp
    let ⟨a₀, ha₀⟩ := s₀_spec n
    let a := (ZMod.chineseRemainderₓ cop).symm (ZMod.unitsMap ⟨k, hpsk⟩ a₀, 1)
    let a' := ZMod.unitsMap (dvd_of_eq hpsk) a
    have aF : a' ∈ F n := by
      suffices a ^ (n - 1) = 1 by
        simpa [a'] using congr(ZMod.unitsMap _ $this)
      suffices a₀ ^ (n - 1) = 1 by
        rw [← map_pow, Prod.pow_mk, one_pow, ← map_pow, this, map_one, ← Prod.one_eq_mk, map_one]
      rw [← two_pow_val₂_mul_oddPart (n - 1), ← Nat.sub_add_cancel (s₀_lt_val₂ ho), pow_add,
        mul_assoc, mul_comm, pow_mul, Nat.pow_succ, mul_right_comm, pow_mul, ha₀]
      simp
    intro hGF
    rw [← hGF, G, mem_comap, powMonoidHom_apply, mem_closure_neg_one] at aF
    rcases aF with h | h <;>
      apply_fun ZMod.unitsMap (dvd_of_eq hpsk.symm) at h <;>
      rw [map_pow, ← MonoidHom.comp_apply, ZMod.unitsMap_comp, ZMod.unitsMap_self,
        MonoidHom.id_apply] at h
    · apply @ZMod.neg_one_ne_one (p ^ s) ⟨hps⟩
      apply_fun ZMod.unitsMap ⟨k, hpsk⟩ at ha₀
      rw [map_pow, ZMod.unitsMap_neg, map_one] at ha₀
      simpa +zetaDelta [ha₀] using congr(ZMod.unitsMap ⟨k, rfl⟩ $h |>.val)
    · apply @ZMod.neg_one_ne_one k ⟨hk⟩
      simpa +zetaDelta using congr(ZMod.unitsMap ⟨p ^ s, mul_comm _ _⟩ $h |>.val).symm
end SPP
