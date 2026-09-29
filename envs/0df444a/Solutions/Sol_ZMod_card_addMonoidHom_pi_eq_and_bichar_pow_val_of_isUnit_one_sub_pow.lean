-- Prove2me | solution 1 for ZMod.card_addMonoidHom_pi_eq_and_bichar_pow_val_of_isUnit_one_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/46a3251e-2ece-5c1f-b700-74f3b43178ed

import Mathlib
import Theorems.Thm_AddCommGroup_natCard_addMonoidHom_eq_of_isAddCyclic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ZMod_card_addMonoidHom_pi_eq_and_bichar_pow_val_of_isUnit_one_sub_pow

set_option autoImplicit false

open scoped BigOperators

namespace HBSol

variable {g d : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)

include hδd in
theorem d_pos : 0 < d := by
  rw [← hδd]; exact Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne (δ i))

include hδd in
theorem dvd_d (i : Fin g) : δ i ∣ d := by
  rw [← hδd]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

noncomputable def ψ (i : Fin g) : ZMod (δ i) →+ ZMod d :=
  ZMod.lift (δ i) ⟨zmultiplesHom (ZMod d) ((d / δ i : ℕ) : ZMod d), by
    show ((δ i : ℕ) : ℤ) • ((d / δ i : ℕ) : ZMod d) = 0
    rw [natCast_zsmul, nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' (dvd_d δ hδd i), ZMod.natCast_self]⟩

theorem ψ_natCast (i : Fin g) (m : ℕ) : ψ δ hδd i (m : ZMod (δ i)) = ((m * (d / δ i) : ℕ) : ZMod d) := by
  have : ((m : ℤ) : ZMod (δ i)) = (m : ZMod (δ i)) := by simp
  rw [← this, ψ, ZMod.lift_coe]
  show (m : ℤ) • ((d / δ i : ℕ) : ZMod d) = _
  rw [natCast_zsmul, nsmul_eq_mul, Nat.cast_mul]

theorem ψ_apply (i : Fin g) (x : ZMod (δ i)) : ψ δ hδd i x = ((x.val * (d / δ i) : ℕ) : ZMod d) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  exact ψ_natCast δ hδd i x.val

include hδd in
theorem val_ψ (i : Fin g) (x : ZMod (δ i)) : (ψ δ hδd i x).val = x.val * (d / δ i) := by
  haveI : NeZero d := ⟨(d_pos δ hδd).ne'⟩
  rw [ψ_apply, ZMod.val_natCast, Nat.mod_eq_of_lt]
  calc x.val * (d / δ i) < δ i * (d / δ i) :=
        Nat.mul_lt_mul_of_lt_of_le (ZMod.val_lt x) le_rfl
          (Nat.div_pos (Nat.le_of_dvd (d_pos δ hδd) (dvd_d δ hδd i)) (Nat.pos_of_ne_zero (NeZero.ne _)))
    _ = d := Nat.mul_div_cancel' (dvd_d δ hδd i)

theorem pow_eq_pow_mod {R : Type*} [CommRing R] (ζ : Rˣ) (hζ : (ζ : R) ^ d = 1) (m : ℕ) : ζ ^ m = ζ ^ (m % d) := by
  have hζ' : ζ ^ d = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hζ, Units.val_one])
  conv_lhs => rw [← Nat.div_add_mod m d, pow_add, pow_mul, hζ', one_pow, one_mul]

theorem isUnit_of_val {R : Type*} [CommRing R] (ζ : Rˣ)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - (ζ : R) ^ j)) (j : ℕ) (hj : 0 < j) (hjd : j < d) :
    IsUnit ((ζ ^ j : R) - 1) := by
  have := (hζu j hj hjd).neg
  rwa [neg_sub] at this

end HBSol

theorem solution
    {g d : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    {R : Type*} [CommRing R] (ζ : Rˣ) (hζ : (ζ : R) ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - (ζ : R) ^ j)) :
    Nat.card (((i : Fin g) → ZMod (δ i)) →+ ZMod d) = Nat.card ((i : Fin g) → ZMod (δ i)) ∧
    (∀ (h₁ h₂ : (i : Fin g) → ZMod (δ i)) (c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d),
      ζ ^ (c (h₁ + h₂)).val = ζ ^ (c h₁).val * ζ ^ (c h₂).val) ∧
    (∀ (h : (i : Fin g) → ZMod (δ i)) (c₁ c₂ : ((i : Fin g) → ZMod (δ i)) →+ ZMod d),
      ζ ^ ((c₁ + c₂) h).val = ζ ^ (c₁ h).val * ζ ^ (c₂ h).val) ∧
    (∀ h : (i : Fin g) → ZMod (δ i), h ≠ 0 → ∃ c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d, IsUnit ((ζ ^ (c h).val : R) - 1)) ∧
    (∀ c : ((i : Fin g) → ZMod (δ i)) →+ ZMod d, c ≠ 0 → ∃ h : (i : Fin g) → ZMod (δ i), IsUnit ((ζ ^ (c h).val : R) - 1)) := by
  classical
  haveI : NeZero d := ⟨(HBSol.d_pos δ hδd).ne'⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    apply AddCommGroup.natCard_addMonoidHom_eq_of_isAddCyclic
    intro x
    rw [Nat.card_zmod]
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, (ZMod.natCast_eq_zero_iff d (δ i)).mpr (HBSol.dvd_d δ hδd i), zero_mul]
  · intro h₁ h₂ c
    rw [map_add, ← pow_add, HBSol.pow_eq_pow_mod ζ hζ ((c h₁).val + (c h₂).val), ZMod.val_add]
  · intro h c₁ c₂
    rw [AddMonoidHom.add_apply, ← pow_add, HBSol.pow_eq_pow_mod ζ hζ ((c₁ h).val + (c₂ h).val), ZMod.val_add]
  · intro h hh
    obtain ⟨i, hi⟩ : ∃ i, h i ≠ 0 := by
      by_contra hall; push Not at hall; exact hh (funext hall)
    refine ⟨(HBSol.ψ δ hδd i).comp (Pi.evalAddMonoidHom (fun j => ZMod (δ j)) i), ?_⟩
    apply HBSol.isUnit_of_val ζ hζu
    · show 0 < (HBSol.ψ δ hδd i (h i)).val
      rw [HBSol.val_ψ δ hδd]
      exact Nat.mul_pos (Nat.pos_of_ne_zero fun h0 => hi ((ZMod.val_eq_zero _).mp h0))
        (Nat.div_pos (Nat.le_of_dvd (HBSol.d_pos δ hδd) (HBSol.dvd_d δ hδd i)) (Nat.pos_of_ne_zero (NeZero.ne _)))
    · exact ZMod.val_lt _
  · intro c hc
    obtain ⟨h, hh⟩ : ∃ h, c h ≠ 0 := by
      by_contra hall; push Not at hall; exact hc (AddMonoidHom.ext hall)
    refine ⟨h, ?_⟩
    exact HBSol.isUnit_of_val ζ hζu _ (Nat.pos_of_ne_zero fun h0 => hh ((ZMod.val_eq_zero _).mp h0)) (ZMod.val_lt _)

end S_ZMod_card_addMonoidHom_pi_eq_and_bichar_pow_val_of_isUnit_one_sub_pow
end P2MW
export P2MW.S_ZMod_card_addMonoidHom_pi_eq_and_bichar_pow_val_of_isUnit_one_sub_pow (solution)
