-- Prove2me | solution 1 for SPP.H_inf_H_lt_H_inf_H_inf_H
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:14:23.548174+00:00
-- url     : https://prove2.me/submissions/5043542b-0d19-42b2-8a08-f700c7af5560

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_P2M_SPP_s__spec_e1afc8f96699
import Theorems.Thm_SPP_H_mul_le_H_inf_H
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
namespace SPP
theorem _root_.solution [NeZero n] {m₁ m₂ m₃ : ℕ}
    (h₁ : 2 < m₁) (h₂ : 2 < m₂) (hc : m₁.Coprime (m₂ * m₃)) (h₁₂₃n : m₁ * m₂ * m₃ ∣ n) :
    H (dvd_of_mul_right_dvd h₁₂₃n) ⊓ H (dvd_of_mul_left_dvd h₁₂₃n) <
      H (dvd_of_mul_right_dvd (dvd_of_mul_right_dvd h₁₂₃n)) ⊓
      H (dvd_of_mul_left_dvd (dvd_of_mul_right_dvd h₁₂₃n)) ⊓ H (dvd_of_mul_left_dvd h₁₂₃n) := by
  have h₁₂n := dvd_of_mul_right_dvd h₁₂₃n
  have h₁n := dvd_of_mul_right_dvd h₁₂n
  have h₂n := dvd_of_mul_left_dvd h₁₂n
  have h₃n := dvd_of_mul_left_dvd h₁₂₃n
  have h₁₂₃'n := mul_assoc m₁ m₂ m₃ ▸ h₁₂₃n
  have h₂₃n := dvd_of_mul_left_dvd h₁₂₃'n
  have hn : Fact (1 < n) := ⟨h₁.le.trans (le_of_dvd (pos_iff_ne_zero.mpr NeZero.out) h₁n)⟩
  apply lt_of_le_of_ne (inf_le_inf_right _ (H_mul_le_H_inf_H h₁₂n))
  intro hH
  let ⟨a₀, ha₀⟩ := s₀_spec n
  let a := (ZMod.chineseRemainderₓ hc).symm (ZMod.unitsMap h₁n a₀, 1)
  let ⟨b, hb⟩ := ZMod.unitsMap_surjective h₁₂₃'n a
  have : b ∈ H h₁₂n := by
    suffices b ∈ H h₁n ⊓ H h₂n ⊓ H h₃n by rw [← hH] at this; exact (mem_inf.mp this).1
    rw [inf_assoc, mem_inf]
    apply And.imp_right fun h ↦ H_mul_le_H_inf_H h₂₃n h
    constructor <;> rw [H, mem_comap, mem_comap, powMonoidHom_apply, mem_closure_neg_one]
    · right
      rw [← ZMod.unitsMap_comp (dvd_mul_right m₁ (m₂ * m₃)) h₁₂₃'n, map_pow, MonoidHom.comp_apply,
        hb, ZMod.unitsMap_chineseRemainderₓ_symm, ← map_pow, ha₀, ZMod.unitsMap_neg, map_one]
    · left
      rw [← ZMod.unitsMap_comp (dvd_mul_left (m₂ * m₃) m₁) h₁₂₃'n, map_pow, MonoidHom.comp_apply,
        hb, ZMod.unitsMap_chineseRemainderₓ_symm', one_pow]
  rw [H, mem_comap, mem_comap, powMonoidHom_apply,
    ← ZMod.unitsMap_comp (mul_assoc m₁ m₂ m₃ ▸ dvd_mul_right (m₁ * m₂) m₃) h₁₂₃'n,
    MonoidHom.comp_apply, map_pow, hb, ← map_pow, Prod.pow_mk, one_pow, ← map_pow, ha₀,
    ZMod.unitsMap_neg, map_one, mem_closure_neg_one] at this
  rcases this with h | h
  · apply_fun (ZMod.unitsMap (dvd_mul_right m₁ m₂) · |>.val) at h
    apply @ZMod.neg_one_ne_one m₁ ⟨h₁⟩
    simpa [← MonoidHom.comp_apply, ZMod.unitsMap_comp] using h
  · apply_fun (ZMod.unitsMap (dvd_mul_left m₂ m₁) · |>.val) at h
    apply @ZMod.neg_one_ne_one m₂ ⟨h₂⟩
    rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp,
      ← ZMod.unitsMap_comp (dvd_mul_right m₂ m₃) (dvd_mul_left (m₂ * m₃) m₁)] at h
    simpa using h.symm
end SPP
