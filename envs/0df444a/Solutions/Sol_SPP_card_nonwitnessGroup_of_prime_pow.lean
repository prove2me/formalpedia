-- Prove2me | solution 1 for SPP.card_nonwitnessGroup_of_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:16:09.185333+00:00
-- url     : https://prove2.me/submissions/fd9495f0-e6f7-41a4-8d46-e4f11d22a66f

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_SPP_isUnit
import Theorems.Thm_SPP_nonwitnessGroup_of_prime_pow
import Theorems.Thm_FPP_isUnit
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
import Theorems.Thm_Subgroup_mem_closure_neg_one
import Theorems.Thm_ZMod_add_mul_prime_pow_pow
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


section
open Nat
namespace SPP
section Algorithm
end Algorithm
section Decidable
end Decidable
section FPP
end FPP
section NonwitnessGroup
open Subgroup
variable {n : ℕ}
section OfPrimePow
variable {m p : ℕ} [pp : Fact p.Prime]
private lemma cast_cast_pow {x : (ZMod (p ^ m))} :
    ((x.cast : ZMod (p ^ (m + 1))).cast : ZMod (p ^ m)) = x :=
  ZMod.cast_cast_zmod_of_le (Nat.pow_lt_pow_right pp.out.one_lt m.lt_succ_self).le _
private lemma lift_unique (hm : 0 < m) (x : (ZMod (p ^ m))ˣ) (hx : x ^ (p - 1) = 1) (y : (ZMod (p ^ (m + 1)))) :
    (y.cast : ZMod (p ^ m)) = x ∧ y ^ (p - 1) = 1 ↔
      y = (x.val.cast : ZMod (p ^ (m + 1))) - p ^ m * rem ((x.val.cast : ZMod (p ^ (m + 1))) ^ (p - 1)) *
        ((x.val.cast : ZMod (p ^ (m + 1))) ^ (p - 2))⁻¹ * (p - 1 : ZMod (p ^ (m + 1)))⁻¹ := by
  have : Fact (1 < p ^ m) := ⟨one_lt_pow hm.ne' pp.out.one_lt⟩
  have := (rem ((x.val.cast : ZMod (p ^ (m + 1))) ^ (p - 1))).2
  nth_rw 1 [← ZMod.castHom_apply (h := pow_dvd_pow p m.lt_succ_self.le)] at this
  rw [RingHom.map_pow, ZMod.castHom_apply, cast_cast_pow, ← sub_eq_iff_eq_add'] at this
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one] at hx
  rw [← this, hx, ZMod.cast_eq_val 1, ZMod.val_one, cast_one]
  have cancel :
      ((x.val.cast : ZMod (p ^ (m + 1))) ^ (p - 2)) * (p - 1) * ((x.val.cast : ZMod (p ^ (m + 1))) ^ (p - 2))⁻¹ *
        ((p : ZMod (p ^ (m + 1))) - 1)⁻¹ = 1 := by
    rw [mul_right_comm (_ ^ _), ZMod.mul_inv_of_unit, one_mul, ZMod.mul_inv_of_unit]
    · have : (p - 1).Coprime (p ^ (m + 1)) := by
        apply Coprime.pow_right
        rw [coprime_self_sub_left pp.out.pos]
        exact coprime_one_left p
      simpa only [ZMod.coe_unitOfCoprime, cast_sub pp.out.pos, cast_one] using
        (ZMod.unitOfCoprime _ this).isUnit
    · by_cases hp : p = 2
      · simp only [hp, Nat.sub_self, _root_.pow_zero, isUnit_one]
      rw [isUnit_pow_iff (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne pp.out.two_le (Ne.symm hp)))]
      have : x.val.val.Coprime (p ^ (m + 1)) := by
        apply Coprime.pow_right
        rw [← coprime_pow_right_iff hm]
        exact ZMod.val_coe_unit_coprime x
      simpa only [ZMod.coe_unitOfCoprime, ZMod.natCast_val] using
        (ZMod.unitOfCoprime _ this).isUnit
  have hrem := (rem (y : ZMod (p ^ (m + 1)))).2
  constructor
  · intro ⟨h₁, h₂⟩
    nth_rw 1 [h₁] at hrem
    rw [hrem, mul_comm, ZMod.add_mul_prime_pow_pow _ _ hm (zero_lt_sub_of_lt pp.out.one_lt), Nat.sub_sub,
      cast_sub pp.out.pos, cast_one, ← eq_sub_iff_add_eq'] at h₂
    rw [hrem, sub_eq_add_neg, add_left_cancel_iff, ← neg_mul, ← neg_mul, neg_sub, ← h₂,
      ← one_mul (_ * _)]
    nth_rw 1 [← cancel]
    ring
  · intro h
    have h₁ := congr((ZMod.castHom (pow_dvd_pow p m.lt_succ_self.le) (ZMod (p ^ m))) $h)
    rw [ZMod.castHom_apply, map_sub, map_mul, map_mul, map_sub, ZMod.castHom_apply, map_pow,
      ZMod.castHom_apply, map_one, ZMod.castHom_apply, cast_cast_pow, hx, sub_self, zero_mul,
      zero_mul, sub_zero] at h₁
    use h₁
    nth_rw 1 [h₁] at hrem
    rw [hrem, sub_eq_add_neg, add_left_cancel_iff, ← neg_mul, ← neg_mul, neg_sub] at h
    rw [hrem, mul_comm, ZMod.add_mul_prime_pow_pow _ _ hm (zero_lt_sub_of_lt pp.out.one_lt), Nat.sub_sub,
      cast_sub pp.out.pos, cast_one, mul_assoc (_ ^ _), mul_comm _ (_ ^ _), h,
      ← eq_sub_iff_add_eq', ← one_mul (1 - _)]
    nth_rw 5 [← cancel]
    ring
private lemma card_ker_powMonoidHom_sub_one_of_prime_pow (hm : 0 < m) :
    Nat.card ((powMonoidHom (p - 1)).ker : Subgroup (ZMod (p ^ m))ˣ) = p - 1 := by
  induction m, hm using Nat.le_induction with
  | base =>
    calc
      _ = Nat.card (ZMod (p ^ 1))ˣ := by
        rw [card_eq_iff_eq_top, eq_top_iff', pow_one]
        intro x
        rw [MonoidHom.mem_ker, powMonoidHom_apply, ZMod.units_pow_card_sub_one_eq_one]
      _ = p - 1 := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, totient_prime pp.out]
  | succ m hm ih =>
    conv_rhs => rw [← ih]
    simp_rw [MonoidHom.mem_ker, powMonoidHom_apply]
    refine Nat.card_congr ⟨?_, ?_, ?_, ?_⟩
    · intro ⟨x, hx⟩
      use ZMod.unitsMap (pow_dvd_pow p m.lt_succ_self.le) x
      rw [← MonoidHom.map_pow, hx, MonoidHom.map_one]
    · intro ⟨x, hx⟩
      let y := (x.val.cast : ZMod (p ^ (m + 1))) - p ^ m * rem ((x.val.cast : ZMod (p ^ (m + 1))) ^ (p - 1)) *
        ((x.val.cast : ZMod (p ^ (m + 1))) ^ (p - 2))⁻¹ * (p - 1 : ZMod (p ^ (m + 1)))⁻¹
      use Units.ofPowEqOne y (p - 1) ((lift_unique hm x hx y).mpr rfl).2 (sub_ne_zero_of_lt pp.out.one_lt)
      exact Units.pow_ofPowEqOne _ _
    · intro ⟨y, hy⟩
      rw [Subtype.mk.injEq, Units.ext_iff]
      let x := ZMod.unitsMap (pow_dvd_pow p m.lt_succ_self.le) y
      refine ((lift_unique hm x ?_ _).mp ⟨rfl, ?_⟩).symm
      · simpa using congr(ZMod.unitsMap (pow_dvd_pow p m.lt_succ_self.le) $hy)
      · simpa [Units.ext_iff] using hy
    · intro ⟨x, hx⟩
      simpa [Units.ext_iff, ZMod.unitsMap_def] using ((lift_unique hm x hx _).mpr rfl).1
end OfPrimePow
section DefS₀G
end DefS₀G
section OfNotCarmichael
end OfNotCarmichael
section OfCarmichael
end OfCarmichael
end NonwitnessGroup
open Finset
section Probability
open MeasureTheory ProbabilityTheory
open scoped ENNReal
end Probability
end SPP
end

set_option autoImplicit false
open Nat
open SPP
open Subgroup
variable {n : ℕ}
variable {m p : ℕ} [pp : Fact p.Prime]
namespace SPP
theorem _root_.solution (hm : 0 < m) (hp : 2 < p) :
    Nat.card (nonwitnessGroup (p ^ m)) = p - 1 := by
  rw [← card_ker_powMonoidHom_sub_one_of_prime_pow hm, nonwitnessGroup_of_prime_pow hm hp]
end SPP
