-- Prove2me | solution 1 for P2mOS.defect_transport_cases
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/404c531e-d9a4-5251-b016-124b3fe649ca

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_P2mOS_defect_transport_cases

set_option autoImplicit false

namespace P2mOSDefect

variable {S : Type*} [CommRing S] {I : Type*} [LinearOrder I]

def T (U U' : I → I → S) (x y : I) : S :=
  if x < y then U x y else if x = y then 1 else U' y x

def T' (U U' : I → I → S) (x y : I) : S :=
  if x < y then U' x y else if x = y then 1 else U y x

section
variable (U U' : I → I → S)

theorem T_of_lt {x y : I} (h : x < y) : T U U' x y = U x y := by simp [T, h]
theorem T_of_eq {x y : I} (h : x = y) : T U U' x y = 1 := by simp [T, h]
theorem T_of_gt {x y : I} (h : y < x) : T U U' x y = U' y x := by
  simp [T, not_lt_of_gt h, ne_of_gt h]
theorem T'_of_lt {x y : I} (h : x < y) : T' U U' x y = U' x y := by simp [T', h]
theorem T'_of_eq {x y : I} (h : x = y) : T' U U' x y = 1 := by simp [T', h]
theorem T'_of_gt {x y : I} (h : y < x) : T' U U' x y = U y x := by
  simp [T', not_lt_of_gt h, ne_of_gt h]

end

theorem eq_one_sub_of_mul_one_add {X D : S} (hD : D * D = 0) (h : X * (1 + D) = 1) : X - 1 = -D := by
  have : X = X * ((1 + D) * (1 - D)) := by
    rw [show (1 + D) * (1 - D) = 1 - D * D by ring, hD, sub_zero, mul_one]
  rw [this, ← mul_assoc, h, one_mul]
  ring

variable (U U' : I → I → S) (hUU' : ∀ p q, p < q → U p q * U' p q = 1)
include hUU'

theorem U'_mul_U {p q : I} (h : p < q) : U' p q * U p q = 1 := by rw [mul_comm, hUU' p q h]

theorem defect_eq_zero_of_not_injective (f : Fin 3 → I) (hf : ¬ Function.Injective f) :
    T U U' (f 0) (f 1) * T U U' (f 1) (f 2) * T' U U' (f 0) (f 2) - 1 = 0 := by
  have hcol : f 0 = f 1 ∨ f 1 = f 2 ∨ f 0 = f 2 := by
    by_contra hne
    push_neg at hne
    apply hf
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd hab hne.1
    · exact absurd hab hne.2.2
    · exact absurd hab.symm hne.1
    · rfl
    · exact absurd hab hne.2.1
    · exact absurd hab.symm hne.2.2
    · exact absurd hab.symm hne.2.1
    · rfl
  rw [sub_eq_zero]
  rcases hcol with h01 | h12 | h02
  · rw [T_of_eq U U' h01, one_mul, h01]
    rcases lt_trichotomy (f 1) (f 2) with h | h | h
    · rw [T_of_lt U U' h, T'_of_lt U U' h, hUU' _ _ h]
    · rw [T_of_eq U U' h, T'_of_eq U U' h, one_mul]
    · rw [T_of_gt U U' h, T'_of_gt U U' h, U'_mul_U U U' hUU' h]
  · rw [T_of_eq U U' h12, mul_one, ← h12]
    rcases lt_trichotomy (f 0) (f 1) with h | h | h
    · rw [T_of_lt U U' h, T'_of_lt U U' h, hUU' _ _ h]
    · rw [T_of_eq U U' h, T'_of_eq U U' h, one_mul]
    · rw [T_of_gt U U' h, T'_of_gt U U' h, U'_mul_U U U' hUU' h]
  · rw [T'_of_eq U U' h02, mul_one, ← h02]
    rcases lt_trichotomy (f 0) (f 1) with h | h | h
    · rw [T_of_lt U U' h, T_of_gt U U' h, hUU' _ _ h]
    · rw [T_of_eq U U' h, T_of_eq U U' h.symm, one_mul]
    · rw [T_of_gt U U' h, T_of_lt U U' h, U'_mul_U U U' hUU' h]

theorem fin3_mk0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
theorem fin3_mk1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
theorem fin3_mk2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl

theorem defect_eq_sign_smul (f : Fin 3 → I) (σ : Equiv.Perm (Fin 3)) (hσ : StrictMono (f ∘ σ))
    (hD : (U (f (σ 0)) (f (σ 1)) * U (f (σ 1)) (f (σ 2)) * U' (f (σ 0)) (f (σ 2)) - 1) *
      (U (f (σ 0)) (f (σ 1)) * U (f (σ 1)) (f (σ 2)) * U' (f (σ 0)) (f (σ 2)) - 1) = 0) :
    T U U' (f 0) (f 1) * T U U' (f 1) (f 2) * T' U U' (f 0) (f 2) - 1 =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ)) •
        (U (f (σ 0)) (f (σ 1)) * U (f (σ 1)) (f (σ 2)) * U' (f (σ 0)) (f (σ 2)) - 1) := by
  have h01 : f (σ 0) < f (σ 1) := hσ (show (0 : Fin 3) < 1 by decide)
  have h12 : f (σ 1) < f (σ 2) := hσ (show (1 : Fin 3) < 2 by decide)
  have h02 : f (σ 0) < f (σ 2) := h01.trans h12
  set D := U (f (σ 0)) (f (σ 1)) * U (f (σ 1)) (f (σ 2)) * U' (f (σ 0)) (f (σ 2)) - 1 with hDdef
  obtain ⟨a, ha⟩ : ∃ a, σ 0 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, σ 1 = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, σ 2 = c := ⟨_, rfl⟩
  have hinj := σ.injective

  have hsign : ∀ τ : Equiv.Perm (Fin 3), τ 0 = a → τ 1 = b → τ 2 = c → Equiv.Perm.sign σ = Equiv.Perm.sign τ := by
    intro τ h0 h1 h2
    congr 1
    ext j
    fin_cases j
    · exact congrArg Fin.val (ha.trans h0.symm)
    · exact congrArg Fin.val (hb.trans h1.symm)
    · exact congrArg Fin.val (hc.trans h2.symm)
  have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> decide
  have hb3 : b = 0 ∨ b = 1 ∨ b = 2 := by fin_cases b <;> decide
  have hc3 : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> decide
  rcases ha3 with rfl | rfl | rfl <;> rcases hb3 with rfl | rfl | rfl <;> rcases hc3 with rfl | rfl | rfl
  all_goals first
    | exact absurd (hinj (ha.trans hb.symm)) (by decide)
    | exact absurd (hinj (hb.trans hc.symm)) (by decide)
    | exact absurd (hinj (ha.trans hc.symm)) (by decide)
    | skip
  all_goals (rw [ha] at h01 h02 hDdef; rw [hb] at h01 h12 hDdef; rw [hc] at h12 h02 hDdef)

  · rw [hsign 1 rfl rfl rfl, Equiv.Perm.sign_one, Units.val_one, one_smul,
      T_of_lt U U' h01, T_of_lt U U' h12, T'_of_lt U U' h02, hDdef]

  · rw [hsign (Equiv.swap 1 2) (by decide) (by decide) (by decide), Equiv.Perm.sign_swap (by decide),
      Units.val_neg, Units.val_one, neg_one_smul,
      T_of_lt U U' h02, T_of_gt U U' h12, T'_of_lt U U' h01]
    apply eq_one_sub_of_mul_one_add hD
    rw [hDdef]
    calc U (f 0) (f 1) * U' (f 2) (f 1) * U' (f 0) (f 2) *
          (1 + (U (f 0) (f 2) * U (f 2) (f 1) * U' (f 0) (f 1) - 1))
        = (U (f 0) (f 1) * U' (f 0) (f 1)) * (U (f 0) (f 2) * U' (f 0) (f 2)) * (U (f 2) (f 1) * U' (f 2) (f 1)) := by ring
      _ = 1 := by rw [hUU' _ _ h02, hUU' _ _ h01, hUU' _ _ h12]; ring

  · rw [hsign (Equiv.swap 0 1) (by decide) (by decide) (by decide), Equiv.Perm.sign_swap (by decide),
      Units.val_neg, Units.val_one, neg_one_smul,
      T_of_gt U U' h01, T_of_lt U U' h02, T'_of_lt U U' h12]
    apply eq_one_sub_of_mul_one_add hD
    rw [hDdef]
    calc U' (f 1) (f 0) * U (f 1) (f 2) * U' (f 0) (f 2) *
          (1 + (U (f 1) (f 0) * U (f 0) (f 2) * U' (f 1) (f 2) - 1))
        = (U (f 1) (f 0) * U' (f 1) (f 0)) * (U (f 0) (f 2) * U' (f 0) (f 2)) * (U (f 1) (f 2) * U' (f 1) (f 2)) := by ring
      _ = 1 := by rw [hUU' _ _ h01, hUU' _ _ h12, hUU' _ _ h02]; ring

  · rw [hsign (Equiv.swap 0 1 * Equiv.swap 1 2) (by decide) (by decide) (by decide), Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide), neg_mul_neg, one_mul, Units.val_one,
      one_smul, T_of_gt U U' h02, T_of_lt U U' h01, T'_of_gt U U' h12, hDdef]
    ring

  · rw [hsign (Equiv.swap 1 2 * Equiv.swap 0 1) (by decide) (by decide) (by decide), Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide), neg_mul_neg, one_mul, Units.val_one,
      one_smul, T_of_lt U U' h12, T_of_gt U U' h02, T'_of_gt U U' h01, hDdef]
    ring

  · rw [hsign (Equiv.swap 0 2) (by decide) (by decide) (by decide), Equiv.Perm.sign_swap (by decide),
      Units.val_neg, Units.val_one, neg_one_smul,
      T_of_gt U U' h12, T_of_gt U U' h01, T'_of_gt U U' h02]
    apply eq_one_sub_of_mul_one_add hD
    rw [hDdef]
    calc U' (f 1) (f 0) * U' (f 2) (f 1) * U (f 2) (f 0) *
          (1 + (U (f 2) (f 1) * U (f 1) (f 0) * U' (f 2) (f 0) - 1))
        = (U (f 1) (f 0) * U' (f 1) (f 0)) * (U (f 2) (f 1) * U' (f 2) (f 1)) * (U (f 2) (f 0) * U' (f 2) (f 0)) := by ring
      _ = 1 := by rw [hUU' _ _ h12, hUU' _ _ h01, hUU' _ _ h02]; ring

end P2mOSDefect

theorem solution
    {S : Type*} [CommRing S] {I : Type*} [LinearOrder I]
    (U U' : I → I → S) (hUU' : ∀ p q, p < q → U p q * U' p q = 1) (f : Fin 3 → I) :
    (¬ Function.Injective f →
      (if f 0 < f 1 then U (f 0) (f 1) else if f 0 = f 1 then 1 else U' (f 1) (f 0)) *
        (if f 1 < f 2 then U (f 1) (f 2) else if f 1 = f 2 then 1 else U' (f 2) (f 1)) *
        (if f 0 < f 2 then U' (f 0) (f 2) else if f 0 = f 2 then 1 else U (f 2) (f 0)) - 1 = 0) ∧
    (∀ σ : Equiv.Perm (Fin 3), StrictMono (f ∘ σ) →
      (U (f (σ 0)) (f (σ 1)) * U (f (σ 1)) (f (σ 2)) * U' (f (σ 0)) (f (σ 2)) - 1) *
        (U (f (σ 0)) (f (σ 1)) * U (f (σ 1)) (f (σ 2)) * U' (f (σ 0)) (f (σ 2)) - 1) = 0 →
      (if f 0 < f 1 then U (f 0) (f 1) else if f 0 = f 1 then 1 else U' (f 1) (f 0)) *
        (if f 1 < f 2 then U (f 1) (f 2) else if f 1 = f 2 then 1 else U' (f 2) (f 1)) *
        (if f 0 < f 2 then U' (f 0) (f 2) else if f 0 = f 2 then 1 else U (f 2) (f 0)) - 1 =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ)) •
        (U (f (σ 0)) (f (σ 1)) * U (f (σ 1)) (f (σ 2)) * U' (f (σ 0)) (f (σ 2)) - 1))  :=
  ⟨fun hf => P2mOSDefect.defect_eq_zero_of_not_injective U U' hUU' f hf,
   fun σ hσ hD => P2mOSDefect.defect_eq_sign_smul U U' hUU' f σ hσ hD⟩

end S_P2mOS_defect_transport_cases
end P2MW
export P2MW.S_P2mOS_defect_transport_cases (solution)
