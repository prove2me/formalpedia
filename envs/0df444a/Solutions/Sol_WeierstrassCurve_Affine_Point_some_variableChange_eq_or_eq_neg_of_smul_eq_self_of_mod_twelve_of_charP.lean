-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.some_variableChange_eq_or_eq_neg_of_smul_eq_self_of_mod_twelve_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3cacbbdf-1439-585f-979b-61b2acc8302a

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_mul_heq
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_one_heq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_some_variableChange_eq_or_eq_neg_of_smul_eq_self_of_mod_twelve_of_charP

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace K2BGuardAut

variable {F : Type*} [Field F]

theorem pow_u (C : VariableChange F) : ∀ k : ℕ, (C ^ k).u = C.u ^ k
  | 0 => by rw [pow_zero, pow_zero]; rfl
  | k + 1 => by
      rw [pow_succ, pow_succ, VariableChange.mul_def]
      dsimp only
      rw [pow_u C k]

theorem pow_smul_eq (C : VariableChange F) (W : WeierstrassCurve F) (hC : C • W = W) :
    ∀ k : ℕ, C ^ k • W = W
  | 0 => by rw [pow_zero, one_smul]
  | k + 1 => by rw [pow_succ, mul_smul, hC, pow_smul_eq C W hC k]

theorem one_mk_mul (r s t r' s' t' : F) :
    (⟨1, r, s, t⟩ : VariableChange F) * ⟨1, r', s', t'⟩ = ⟨1, r + r', s + s', t + r * s' + t'⟩ := by
  rw [VariableChange.mul_def]
  ext <;> dsimp only <;> push_cast <;> ring

theorem one_mk_pow_three (r s t : F) :
    (⟨1, r, s, t⟩ : VariableChange F) ^ 3 = ⟨1, 3 * r, 3 * s, 3 * t + 3 * (r * s)⟩ := by
  rw [pow_succ, pow_two, one_mk_mul, one_mk_mul]
  ext <;> dsimp only <;> ring

theorem one_mk_pow_four (r s t : F) :
    (⟨1, r, s, t⟩ : VariableChange F) ^ 4 = ⟨1, 4 * r, 4 * s, 4 * t + 6 * (r * s)⟩ := by
  rw [pow_succ, one_mk_pow_three, one_mk_mul]
  ext <;> dsimp only <;> ring

theorem eq_one_mk (D : VariableChange F) (hD : D.u = 1) : D = ⟨1, D.r, D.s, D.t⟩ := by
  ext <;> dsimp only
  rw [hD]

theorem pow_twelve_eq_one (W : WeierstrassCurve F) [W.IsElliptic] (C : VariableChange F)
    (hC : C • W = W) : C ^ 12 = 1 := by

  have hΔ : (C • W).Δ = ↑C.u⁻¹ ^ 12 * W.Δ := W.variableChange_Δ C
  rw [hC] at hΔ
  have hΔ0 : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  have hv12 : ((C.u⁻¹ : Fˣ) : F) ^ 12 = 1 := by
    have h0 : (((C.u⁻¹ : Fˣ) : F) ^ 12 - 1) * W.Δ = 0 := by linear_combination (-1 : F) * hΔ
    rcases mul_eq_zero.mp h0 with h1 | h1
    · linear_combination h1
    · exact absurd h1 hΔ0
  have hu12 : (C.u : F) ^ 12 = 1 := by
    have e : (C.u : F) = (((C.u⁻¹ : Fˣ) : F))⁻¹ := by rw [Units.val_inv_eq_inv_val, inv_inv]
    rw [e, inv_pow, hv12, inv_one]
  have hUpow : ∀ k : ℕ, (C.u : F) ^ k = 1 → (C ^ k).u = 1 := fun k hk =>
    Units.ext (by rw [pow_u, Units.val_pow_eq_pow_val, Units.val_one]; exact hk)
  by_cases h2 : (2 : F) = 0
  ·
    have hu3 : (C.u : F) ^ 3 = 1 := by
      have h4 : ((C.u : F) ^ 3 - 1) ^ 4 = 0 := by
        linear_combination hu12 - (2 * (C.u : F) ^ 9 - 3 * (C.u : F) ^ 6 + 2 * (C.u : F) ^ 3 - 1) * h2
      exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h4)
    have hD := eq_one_mk (C ^ 3) (hUpow 3 hu3)
    rw [show (12 : ℕ) = 3 * 4 from rfl, pow_mul, hD, one_mk_pow_four, VariableChange.one_def]
    ext <;> dsimp only
    · linear_combination (2 * (C ^ 3).r) * h2
    · linear_combination (2 * (C ^ 3).s) * h2
    · linear_combination (2 * (C ^ 3).t + 3 * ((C ^ 3).r * (C ^ 3).s)) * h2
  · by_cases h3 : (3 : F) = 0
    ·
      have hu4 : (C.u : F) ^ 4 = 1 := by
        have h4 : ((C.u : F) ^ 4 - 1) ^ 3 = 0 := by
          linear_combination hu12 - ((C.u : F) ^ 8 - (C.u : F) ^ 4) * h3
        exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h4)
      have hD := eq_one_mk (C ^ 4) (hUpow 4 hu4)
      rw [show (12 : ℕ) = 4 * 3 from rfl, pow_mul, hD, one_mk_pow_three, VariableChange.one_def]
      ext <;> dsimp only
      · linear_combination ((C ^ 4).r) * h3
      · linear_combination ((C ^ 4).s) * h3
      · linear_combination ((C ^ 4).t + (C ^ 4).r * (C ^ 4).s) * h3
    ·
      have hDu : (C ^ 12).u = 1 := hUpow 12 hu12
      have hD : C ^ 12 • W = W := pow_smul_eq C W hC 12
      have e1 := congrArg WeierstrassCurve.a₁ hD
      have e2 := congrArg WeierstrassCurve.a₂ hD
      have e3 := congrArg WeierstrassCurve.a₃ hD
      rw [variableChange_a₁, hDu, inv_one, Units.val_one, one_mul] at e1
      rw [variableChange_a₂, hDu, inv_one, Units.val_one, one_pow, one_mul] at e2
      rw [variableChange_a₃, hDu, inv_one, Units.val_one, one_pow, one_mul] at e3
      have hs : (C ^ 12).s = 0 := by
        have : (2 : F) * (C ^ 12).s = 0 := by linear_combination e1
        exact (mul_eq_zero.mp this).resolve_left h2
      have hr : (C ^ 12).r = 0 := by
        have : (3 : F) * (C ^ 12).r = 0 := by
          linear_combination e2 + (W.a₁ + (C ^ 12).s) * hs
        exact (mul_eq_zero.mp this).resolve_left h3
      have ht : (C ^ 12).t = 0 := by
        have : (2 : F) * (C ^ 12).t = 0 := by linear_combination e3 - W.a₁ * hr
        exact (mul_eq_zero.mp this).resolve_left h2
      rw [eq_one_mk (C ^ 12) hDu, hr, hs, ht, VariableChange.one_def]

section Transport

theorem pt_congr {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) :
    W₁.toAffine.Point = W₂.toAffine.Point := by rw [e]

theorem some_heq {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) (x y : F)
    (h₁ : W₁.toAffine.Nonsingular x y) (h₂ : W₂.toAffine.Nonsingular x y) :
    HEq (Point.some (W' := W₁.toAffine) x y h₁) (Point.some (W' := W₂.toAffine) x y h₂) := by
  subst e; rfl

theorem vcInvFun_heq_of_eq {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) (C : VariableChange F)
    (P : W₁.toAffine.Point) :
    HEq (Point.vcInvFun C W₁.toAffine P) (Point.vcInvFun C W₂.toAffine (cast (pt_congr e) P)) := by
  subst e; rfl

noncomputable def T (C : VariableChange F) (W : WeierstrassCurve F) (hC : C • W = W)
    (P : W.toAffine.Point) : W.toAffine.Point :=
  cast (pt_congr hC) (Point.vcInvFun C W.toAffine P)

theorem T_congr {C₁ C₂ : VariableChange F} (e : C₁ = C₂) (W : WeierstrassCurve F)
    (h₁ : C₁ • W = W) (h₂ : C₂ • W = W) (P : W.toAffine.Point) : T C₁ W h₁ P = T C₂ W h₂ P := by
  subst e; rfl

theorem T_some (C : VariableChange F) (W : WeierstrassCurve F) (hC : C • W = W) {x y : F}
    (h : W.toAffine.Nonsingular x y) {x' y' : F} (h' : W.toAffine.Nonsingular x' y')
    (hx : x' = vcXInv C x) (hy : y' = vcYInv C x y) :
    T C W hC (Point.some x y h) = Point.some x' y' h' := by
  subst hx hy
  unfold T Point.vcInvFun
  exact cast_eq_iff_heq.mpr (some_heq hC _ _ _ _)

variable [DecidableEq F]

theorem cast_add {W₁ W₂ : WeierstrassCurve F} (e : W₁ = W₂) (P Q : W₁.toAffine.Point) :
    cast (pt_congr e) (P + Q) = cast (pt_congr e) P + cast (pt_congr e) Q := by
  subst e; rfl

theorem T_add (C : VariableChange F) (W : WeierstrassCurve F) (hC : C • W = W)
    (P Q : W.toAffine.Point) : T C W hC (P + Q) = T C W hC P + T C W hC Q := by
  unfold T
  rw [Point.vcInvFun_add, cast_add hC]

theorem T_zsmul (C : VariableChange F) (W : WeierstrassCurve F) (hC : C • W = W)
    (n : ℤ) (P : W.toAffine.Point) : T C W hC (n • P) = n • T C W hC P :=
  map_zsmul (AddMonoidHom.mk' (T C W hC) (T_add C W hC)) n P

theorem T_one (W : WeierstrassCurve F) (h1 : (1 : VariableChange F) • W = W)
    (P : W.toAffine.Point) : T 1 W h1 P = P := by
  unfold T
  exact cast_eq_iff_heq.mpr (Point.vcInvFun_one_heq W.toAffine P)

theorem T_mul (C₁ C₂ : VariableChange F) (W : WeierstrassCurve F) (h₁ : C₁ • W = W)
    (h₂ : C₂ • W = W) (h₁₂ : (C₁ * C₂) • W = W) (P : W.toAffine.Point) :
    T (C₁ * C₂) W h₁₂ P = T C₁ W h₁ (T C₂ W h₂ P) := by
  unfold T
  apply eq_of_heq
  refine (cast_heq _ _).trans ?_
  refine (Point.vcInvFun_mul_heq C₁ C₂ W.toAffine P).trans ?_
  refine (vcInvFun_heq_of_eq h₂ C₁ _).trans ?_
  exact (cast_heq _ _).symm

theorem T_iterate (C : VariableChange F) (W : WeierstrassCurve F) (hC : C • W = W) :
    ∀ (k : ℕ) (P : W.toAffine.Point),
      (T C W hC)^[k] P = T (C ^ k) W (pow_smul_eq C W hC k) P
  | 0, P => by
      rw [Function.iterate_zero, id_eq, T_congr (pow_zero C) W _ (one_smul _ W), T_one]
  | k + 1, P => by
      rw [Function.iterate_succ_apply, T_iterate C W hC k,
        T_congr (pow_succ C k) W _ ((mul_smul (C ^ k) C W).trans
          ((congrArg (C ^ k • ·) hC).trans (pow_smul_eq C W hC k))),
        T_mul (C ^ k) C W (pow_smul_eq C W hC k) hC]

end Transport

theorem int_modEq_one_or_neg_one (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (n : ℤ)
    (h12 : (ℓ : ℤ) ∣ n ^ 12 - 1) (hn : ¬ (ℓ : ℤ) ∣ n) :
    (ℓ : ℤ) ∣ n - 1 ∨ (ℓ : ℤ) ∣ n + 1 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hm0 : (n : ZMod ℓ) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hm12 : (n : ZMod ℓ) ^ 12 = 1 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (n ^ 12 - 1) ℓ).mpr h12
    push_cast at h
    exact sub_eq_zero.mp h
  have hmF : (n : ZMod ℓ) ^ (ℓ - 1) = 1 := ZMod.pow_card_sub_one_eq_one hm0
  have hq : ℓ - 1 = 12 * (ℓ / 12) + 10 := by
    have := Nat.div_add_mod ℓ 12
    omega
  have hm2 : (n : ZMod ℓ) ^ 2 = 1 := by
    have e1 : (n : ZMod ℓ) ^ (12 * (ℓ / 12 + 1)) = 1 := by rw [pow_mul, hm12, one_pow]
    have e2 : 12 * (ℓ / 12 + 1) = (12 * (ℓ / 12) + 10) + 2 := by ring
    rw [e2, pow_add, ← hq, hmF, one_mul] at e1
    exact e1
  rcases sq_eq_one_iff.mp hm2 with h1 | h1
  · left
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 n ℓ).mp (by push_cast; exact h1.symm)
    exact h
  · right
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub (-1) n ℓ).mp (by push_cast; exact h1.symm)
    simpa [sub_neg_eq_add] using h

end K2BGuardAut

open K2BGuardAut in

theorem solution
    {F : Type*} [Field F] [DecidableEq F] (p : ℕ) [Fact p.Prime] [CharP F p] (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) (hC : C • W = W)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11)
    {x y : F} (h : W.toAffine.Nonsingular x y)
    (hℓP : ℓ • WeierstrassCurve.Affine.Point.some x y h = 0)
    (h' : W.toAffine.Nonsingular (((C.u⁻¹ : Fˣ) : F) ^ 2 * (x - C.r)) (((C.u⁻¹ : Fˣ) : F) ^ 3 * (y - C.s * (x - C.r) - C.t)))
    (n : ℤ) (hn : WeierstrassCurve.Affine.Point.some _ _ h' = n • WeierstrassCurve.Affine.Point.some x y h) :
    WeierstrassCurve.Affine.Point.some _ _ h' = WeierstrassCurve.Affine.Point.some x y h ∨
      WeierstrassCurve.Affine.Point.some _ _ h' = -WeierstrassCurve.Affine.Point.some x y h := by
  have h12 : C ^ 12 = 1 := pow_twelve_eq_one W C hC
  have hT : T C W hC (WeierstrassCurve.Affine.Point.some x y h) =
      WeierstrassCurve.Affine.Point.some _ _ h' :=
    T_some C W hC h h' rfl (by simp only [vcYInv]; ring)
  have hTP : T C W hC (WeierstrassCurve.Affine.Point.some x y h) =
      n • WeierstrassCurve.Affine.Point.some x y h := hT.trans hn
  have iter : ∀ k : ℕ, (T C W hC)^[k] (WeierstrassCurve.Affine.Point.some x y h) =
      (n ^ k) • WeierstrassCurve.Affine.Point.some x y h := by
    intro k
    induction k with
    | zero => rw [Function.iterate_zero, id_eq, pow_zero, one_smul]
    | succ k ih => rw [Function.iterate_succ_apply', ih, T_zsmul, hTP, smul_smul, ← pow_succ]
  have hfix : (n ^ 12) • WeierstrassCurve.Affine.Point.some x y h =
      WeierstrassCurve.Affine.Point.some x y h := by
    rw [← iter 12, T_iterate C W hC 12, T_congr h12 W _ (one_smul _ W), T_one]
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hord : addOrderOf (WeierstrassCurve.Affine.Point.some x y h) = ℓ :=
    addOrderOf_eq_prime_iff.mpr ⟨hℓP, WeierstrassCurve.Affine.Point.some_ne_zero h⟩
  have hdvd12 : (ℓ : ℤ) ∣ n ^ 12 - 1 := by
    rw [← hord, addOrderOf_dvd_iff_zsmul_eq_zero, sub_smul, one_smul, hfix, sub_self]
  have hndvd : ¬ (ℓ : ℤ) ∣ n := by
    intro hd
    rw [← hord, addOrderOf_dvd_iff_zsmul_eq_zero, ← hn] at hd
    exact WeierstrassCurve.Affine.Point.some_ne_zero h' hd
  rcases int_modEq_one_or_neg_one ℓ hℓ hℓ12 n hdvd12 hndvd with h1 | h1
  · left
    rw [← hord, addOrderOf_dvd_iff_zsmul_eq_zero, sub_smul, one_smul, sub_eq_zero] at h1
    rw [hn, h1]
  · right
    rw [← hord, addOrderOf_dvd_iff_zsmul_eq_zero, add_smul, one_smul,
      add_eq_zero_iff_eq_neg] at h1
    rw [hn, h1]

end S_WeierstrassCurve_Affine_Point_some_variableChange_eq_or_eq_neg_of_smul_eq_self_of_mod_twelve_of_charP
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_some_variableChange_eq_or_eq_neg_of_smul_eq_self_of_mod_twelve_of_charP (solution)
