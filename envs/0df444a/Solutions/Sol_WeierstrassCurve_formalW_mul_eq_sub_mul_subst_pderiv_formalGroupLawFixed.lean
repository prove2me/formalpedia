-- Prove2me | solution 1 for WeierstrassCurve.formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7a4b798a-7a7f-5dcd-8efe-6e694c3f9ef8

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_MvPowerSeries_pderiv_mul
import Theorems.Thm_MvPowerSeries_pderiv_subst
import Theorems.Thm_WeierstrassCurve_subst_fgInv_formalW_mul_fgInvDenom
import Theorems.Thm_WeierstrassCurve_subst_zero_X_fgSlope
import Theorems.Thm_WeierstrassCurve_subst_zero_X_pderiv_fgSlope
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed

set_option autoImplicit false

open FormalGroup

namespace DW2KEY

open MvPowerSeries

variable {R : Type*} [CommRing R]

theorem pderiv_C {σ : Type*} (i : σ) (c : R) : MvPowerSeries.pderivLin i (MvPowerSeries.C c : MvPowerSeries σ R) = 0 := by
  classical
  ext d
  rw [MvPowerSeries.kw_coeff_pderiv, MvPowerSeries.coeff_C, if_neg, smul_zero, MvPowerSeries.coeff_zero]
  intro h
  have := congrArg (fun e => e i) h
  simp at this

theorem pderiv_one {σ : Type*} (i : σ) : MvPowerSeries.pderivLin i (1 : MvPowerSeries σ R) = 0 := by
  rw [show (1 : MvPowerSeries σ R) = MvPowerSeries.C 1 from (map_one _).symm, pderiv_C]

theorem pderiv_X_self {σ : Type*} [DecidableEq σ] (i : σ) : MvPowerSeries.pderivLin i (MvPowerSeries.X i : MvPowerSeries σ R) = 1 := by
  ext d
  rw [MvPowerSeries.kw_coeff_pderiv, MvPowerSeries.coeff_X, MvPowerSeries.coeff_one]
  by_cases hd : d = 0
  · subst hd; simp
  · rw [if_neg hd, if_neg, smul_zero]
    intro h
    apply hd
    have : d + Finsupp.single i 1 - Finsupp.single i 1 = Finsupp.single i 1 - Finsupp.single i 1 := by rw [h]
    simpa using this

theorem pderiv_X_ne {σ : Type*} [DecidableEq σ] {i j : σ} (hij : i ≠ j) :
    MvPowerSeries.pderivLin i (MvPowerSeries.X j : MvPowerSeries σ R) = 0 := by
  ext d
  rw [MvPowerSeries.kw_coeff_pderiv, MvPowerSeries.coeff_X, if_neg, smul_zero, MvPowerSeries.coeff_zero]
  intro h
  have := congrArg (fun e => e i) h
  simp [hij.symm] at this

theorem pderiv_C_mul {σ : Type*} (i : σ) (c : R) (f : MvPowerSeries σ R) :
    MvPowerSeries.pderivLin i (MvPowerSeries.C c * f) = MvPowerSeries.C c * MvPowerSeries.pderivLin i f := by
  rw [MvPowerSeries.pderiv_mul, pderiv_C, zero_mul, _root_.zero_add]

theorem pderiv_unit_eq_derivative (f : PowerSeries R) :
    MvPowerSeries.pderivLin () f = PowerSeries.derivative R f := by
  ext n
  rw [show PowerSeries.coeff n (MvPowerSeries.pderivLin () f) = MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.pderivLin () f)
      from rfl, MvPowerSeries.kw_coeff_pderiv, PowerSeries.coeff_derivative, Finsupp.single_apply, if_pos rfl,
    ← Finsupp.single_add, show MvPowerSeries.coeff (Finsupp.single () (n + 1)) f = PowerSeries.coeff (n + 1) f from rfl,
    nsmul_eq_mul, mul_comm]
  push_cast
  ring

theorem subst_zero_eq_C {τ : Type*} (h : PowerSeries R) :
    PowerSeries.subst (0 : MvPowerSeries τ R) h = MvPowerSeries.C (PowerSeries.constantCoeff h) := by
  classical
  ext d
  rw [PowerSeries.coeff_subst PowerSeries.HasSubst.zero, MvPowerSeries.coeff_C]
  by_cases hd : d = 0
  · subst hd
    rw [if_pos rfl, finsum_eq_single _ 0 (fun n hn => by rw [zero_pow hn, map_zero, smul_zero])]
    simp
  · rw [if_neg hd]
    apply finsum_eq_zero_of_forall_eq_zero
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero, MvPowerSeries.coeff_one, if_neg hd, smul_zero]
    · rw [zero_pow hn.ne', map_zero, smul_zero]

theorem pderiv_inv_of_mul_eq_one {σ : Type*} (i : σ) {u v : MvPowerSeries σ R} (h : u * v = 1) :
    MvPowerSeries.pderivLin i v = -(MvPowerSeries.pderivLin i u) * v ^ 2 := by
  have h1 := congrArg (MvPowerSeries.pderivLin i) h
  rw [MvPowerSeries.pderiv_mul, pderiv_one] at h1

  have h2 := congrArg (fun t => t * v) h1
  simp only [zero_mul, add_mul] at h2
  linear_combination h2 - (MvPowerSeries.pderivLin i v) * h

end DW2KEY

namespace DW2KEY

open MvPowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

theorem hE : MvPowerSeries.HasSubst (![(0 : PowerSeries R), PowerSeries.X] : Fin 2 → PowerSeries R) :=
  FormalGroup.hasSubst_invDiff (R := R)

local notation "E" => MvPowerSeries.subst (![(0 : PowerSeries R), PowerSeries.X] : Fin 2 → PowerSeries R)

theorem E_X0 : E (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) = 0 := by
  rw [MvPowerSeries.subst_X hE]; rfl

theorem E_X1 : E (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) = PowerSeries.X := by
  rw [MvPowerSeries.subst_X hE]; rfl

theorem E_C (c : R) : E (MvPowerSeries.C c : MvPowerSeries (Fin 2) R) = PowerSeries.C c := by
  rw [MvPowerSeries.subst_C]; rfl

theorem E_mul (f g : MvPowerSeries (Fin 2) R) : E (f * g) = E f * E g := MvPowerSeries.subst_mul hE f g
theorem E_add (f g : MvPowerSeries (Fin 2) R) : E (f + g) = E f + E g := MvPowerSeries.subst_add hE f g
theorem E_neg (f : MvPowerSeries (Fin 2) R) : E (-f) = -E f := by
  rw [← MvPowerSeries.coe_substAlgHom hE, map_neg]
theorem E_sub (f g : MvPowerSeries (Fin 2) R) : E (f - g) = E f - E g := by
  rw [← MvPowerSeries.coe_substAlgHom hE, map_sub]
theorem E_zero' : E (0 : MvPowerSeries (Fin 2) R) = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom hE, map_zero]
theorem E_one : E (1 : MvPowerSeries (Fin 2) R) = 1 := by
  rw [← MvPowerSeries.coe_substAlgHom hE, map_one]
theorem E_pow (f : MvPowerSeries (Fin 2) R) (n : ℕ) : E (f ^ n) = (E f) ^ n := by
  rw [← MvPowerSeries.coe_substAlgHom hE, map_pow]

noncomputable def lam0 : PowerSeries R := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) W.formalW
noncomputable def mu : PowerSeries R := PowerSeries.mk fun n => PowerSeries.coeff (n + 2) W.formalW

theorem X_mul_lam0 : PowerSeries.X * lam0 W = W.formalW := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [PowerSeries.coeff_zero_X_mul, W.coeff_formalW_zero]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [PowerSeries.coeff_succ_X_mul, lam0, PowerSeries.coeff_mk]

theorem X_mul_mu : PowerSeries.X * mu W = lam0 W := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [PowerSeries.coeff_zero_X_mul, lam0, PowerSeries.coeff_mk, _root_.zero_add, W.coeff_formalW_one]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [PowerSeries.coeff_succ_X_mul, mu, lam0, PowerSeries.coeff_mk, PowerSeries.coeff_mk]

theorem chart_lam0 : lam0 W = PowerSeries.X ^ 2 + PowerSeries.C W.a₁ * PowerSeries.X * lam0 W
    + PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * lam0 W + PowerSeries.C W.a₃ * PowerSeries.X * lam0 W ^ 2
    + PowerSeries.C W.a₄ * PowerSeries.X ^ 2 * lam0 W ^ 2 + PowerSeries.C W.a₆ * PowerSeries.X ^ 2 * lam0 W ^ 3 := by
  have h := W.formalW_eq
  rw [← X_mul_lam0] at h
  apply PowerSeries.X_mul_cancel
  linear_combination h

end DW2KEY

namespace DW2KEY

open MvPowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

local notation "E" => MvPowerSeries.subst (![(0 : PowerSeries R), PowerSeries.X] : Fin 2 → PowerSeries R)
local notation "∂" => MvPowerSeries.pderivLin (R := R) (0 : Fin 2)

noncomputable def Den0 : PowerSeries R :=
  1 + PowerSeries.C W.a₂ * lam0 W + PowerSeries.C W.a₄ * lam0 W ^ 2 + PowerSeries.C W.a₆ * lam0 W ^ 3

omit W in

theorem E_psubst (a : MvPowerSeries (Fin 2) R) (ha : MvPowerSeries.constantCoeff a = 0) (h : PowerSeries R) :
    E (PowerSeries.subst a h) = PowerSeries.subst (E a) h := by
  show MvPowerSeries.subst _ (MvPowerSeries.subst (fun _ : Unit => a) h) = MvPowerSeries.subst (fun _ : Unit => E a) h
  rw [MvPowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero ha)) hE]

theorem E_fgW₁ : E W.fgW₁ = 0 := by
  unfold WeierstrassCurve.fgW₁
  rw [E_psubst _ (MvPowerSeries.constantCoeff_X 0), E_X0, subst_zero_eq_C, W.constantCoeff_formalW, map_zero]

theorem E_fgSlope : E W.fgSlope = lam0 W := W.subst_zero_X_fgSlope

theorem E_fgNu : E W.fgNu = 0 := by
  unfold WeierstrassCurve.fgNu
  rw [E_sub, E_mul, E_fgW₁, E_X0, mul_zero, sub_zero]

theorem E_fgZ3Denom : E W.fgZ3Denom = Den0 W := by
  unfold WeierstrassCurve.fgZ3Denom Den0
  simp only [E_add, E_one, E_mul, E_C, E_pow, E_fgSlope]

theorem E_fgZ3NumFixed : E W.fgZ3NumFixed = -(PowerSeries.C W.a₁ * lam0 W + PowerSeries.C W.a₃ * lam0 W ^ 2) := by
  unfold WeierstrassCurve.fgZ3NumFixed
  simp only [E_neg, E_add, E_mul, E_C, E_pow, E_fgSlope, E_fgNu]
  ring

theorem E_pderiv_fgW₁ : E (∂ W.fgW₁) = 0 := by
  unfold WeierstrassCurve.fgW₁
  rw [MvPowerSeries.pderiv_subst 0 _ (MvPowerSeries.constantCoeff_X 0), E_mul,
    E_psubst _ (MvPowerSeries.constantCoeff_X 0), E_X0, subst_zero_eq_C,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, W.coeff_formalW_one]
  simp

theorem E_pderiv_fgSlope : E (∂ W.fgSlope) = mu W := W.subst_zero_X_pderiv_fgSlope

theorem E_pderiv_fgNu : E (∂ W.fgNu) = -lam0 W := by
  unfold WeierstrassCurve.fgNu
  rw [map_sub, MvPowerSeries.pderiv_mul, pderiv_X_self]
  simp only [E_sub, E_add, E_mul, E_one, E_pderiv_fgW₁, E_X0, E_fgSlope, E_pderiv_fgSlope]
  ring

theorem E_pderiv_fgZ3Denom : E (∂ W.fgZ3Denom) =
    (PowerSeries.C W.a₂ + 2 * PowerSeries.C W.a₄ * lam0 W + 3 * PowerSeries.C W.a₆ * lam0 W ^ 2) * mu W := by
  unfold WeierstrassCurve.fgZ3Denom
  rw [pow_two, pow_succ, pow_two]
  simp only [map_add, pderiv_one, pderiv_C, MvPowerSeries.pderiv_mul,
    E_add, E_zero', E_mul, E_C, E_fgSlope, E_pderiv_fgSlope, zero_mul, _root_.zero_add]
  ring

theorem E_pderiv_fgZ3NumFixed : E (∂ W.fgZ3NumFixed) =
    -(PowerSeries.C W.a₁ * mu W + 2 * PowerSeries.C W.a₃ * lam0 W * mu W - PowerSeries.C W.a₂ * lam0 W
      - PowerSeries.C (2 * W.a₄) * lam0 W ^ 2 - PowerSeries.C (3 * W.a₆) * lam0 W ^ 3) := by
  unfold WeierstrassCurve.fgZ3NumFixed
  rw [pow_two, pow_two]
  simp only [map_neg, map_add, pderiv_C, MvPowerSeries.pderiv_mul,
    E_neg, E_add, E_zero', E_mul, E_C, E_fgSlope, E_pderiv_fgSlope, E_fgNu, E_pderiv_fgNu, zero_mul, _root_.zero_add]
  ring

end DW2KEY

namespace DW2KEY

open MvPowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

local notation "E" => MvPowerSeries.subst (![(0 : PowerSeries R), PowerSeries.X] : Fin 2 → PowerSeries R)
local notation "∂" => MvPowerSeries.pderivLin (R := R) (0 : Fin 2)

theorem fgZ3Denom_mul_inv : W.fgZ3Denom * MvPowerSeries.invOfUnit W.fgZ3Denom (1 : Rˣ) = 1 := by
  apply MvPowerSeries.mul_invOfUnit
  unfold WeierstrassCurve.fgZ3Denom
  simp [W.constantCoeff_fgSlope]

theorem fgInvDenom_mul_inv : W.fgInvDenom * PowerSeries.invOfUnit W.fgInvDenom (1 : Rˣ) = 1 := by
  apply PowerSeries.mul_invOfUnit
  unfold WeierstrassCurve.fgInvDenom
  simp [W.constantCoeff_formalW]

theorem fgInv_eq : W.fgInv = -PowerSeries.X * PowerSeries.invOfUnit W.fgInvDenom (1 : Rˣ) := rfl

theorem fgInvDenom_eq : W.fgInvDenom = 1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * W.formalW := rfl

theorem Den0_mul_EDI : Den0 W * E (MvPowerSeries.invOfUnit W.fgZ3Denom (1 : Rˣ)) = 1 := by
  rw [← E_fgZ3Denom, ← E_mul, fgZ3Denom_mul_inv, E_one]

theorem E_fgZ3Fixed_mul_fgInvDenom : E W.fgZ3Fixed * W.fgInvDenom = -PowerSeries.X := by
  have hchart := chart_lam0 W
  have hDI := Den0_mul_EDI W
  have hw := X_mul_lam0 W
  unfold WeierstrassCurve.fgZ3Fixed
  rw [E_add, E_sub, E_neg, E_X0, E_X1, E_mul, E_fgZ3NumFixed, fgInvDenom_eq, ← hw]
  unfold Den0 at hDI
  set DI := E (MvPowerSeries.invOfUnit W.fgZ3Denom (1 : Rˣ)) with hDIdef
  linear_combination (PowerSeries.X * (-(PowerSeries.C W.a₁ * PowerSeries.X) - PowerSeries.C W.a₃ * (PowerSeries.X * lam0 W))) * hDI
    + (DI * (-(lam0 W * PowerSeries.C W.a₃) - PowerSeries.C W.a₁)) * hchart

theorem E_fgZ3Fixed : E W.fgZ3Fixed = W.fgInv := by
  have h := E_fgZ3Fixed_mul_fgInvDenom W
  have hd := fgInvDenom_mul_inv W
  rw [fgInv_eq]
  calc E W.fgZ3Fixed = E W.fgZ3Fixed * (W.fgInvDenom * PowerSeries.invOfUnit W.fgInvDenom (1 : Rˣ)) := by rw [hd, mul_one]
    _ = (E W.fgZ3Fixed * W.fgInvDenom) * PowerSeries.invOfUnit W.fgInvDenom (1 : Rˣ) := by ring
    _ = -PowerSeries.X * PowerSeries.invOfUnit W.fgInvDenom (1 : Rˣ) := by rw [h]

theorem E_pderiv_fgZ3Fixed : E (∂ W.fgZ3Fixed) =
    -1 + E (∂ W.fgZ3NumFixed) * E (MvPowerSeries.invOfUnit W.fgZ3Denom (1 : Rˣ))
      - E W.fgZ3NumFixed * E (∂ W.fgZ3Denom) * E (MvPowerSeries.invOfUnit W.fgZ3Denom (1 : Rˣ)) ^ 2 := by
  unfold WeierstrassCurve.fgZ3Fixed
  rw [map_add, map_sub, map_neg, pderiv_X_self, pderiv_X_ne (show (0 : Fin 2) ≠ 1 by decide),
    MvPowerSeries.pderiv_mul, pderiv_inv_of_mul_eq_one 0 (fgZ3Denom_mul_inv W)]
  simp only [E_add, E_sub, E_neg, E_mul, E_one, E_zero', E_pow]
  ring

theorem E_pderiv_formalGroupLawFixed : E (∂ W.formalGroupLawFixed) =
    PowerSeries.subst W.fgInv (PowerSeries.derivative R W.fgInv) * E (∂ W.fgZ3Fixed) := by
  unfold WeierstrassCurve.formalGroupLawFixed
  rw [MvPowerSeries.pderiv_subst 0 _ W.constantCoeff_fgZ3Fixed, E_mul, E_psubst _ W.constantCoeff_fgZ3Fixed,
    E_fgZ3Fixed]

end DW2KEY

namespace DW2KEY

open MvPowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

omit W in

theorem deriv_inv_of_mul_eq_one {u v : PowerSeries R} (h : u * v = 1) :
    PowerSeries.derivative R v = -(PowerSeries.derivative R u) * v ^ 2 := by
  have h1 := congrArg (PowerSeries.derivative R) h
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, Derivation.map_one_eq_zero] at h1
  have h2 := congrArg (fun t => t * v) h1
  simp only [zero_mul, add_mul] at h2
  linear_combination h2 - (PowerSeries.derivative R v) * h

theorem derivative_fgInvDenom : PowerSeries.derivative R W.fgInvDenom =
    -PowerSeries.C W.a₁ - PowerSeries.C W.a₃ * PowerSeries.derivative R W.formalW := by
  rw [fgInvDenom_eq, map_sub, map_sub, Derivation.map_one_eq_zero, Derivation.leibniz, Derivation.leibniz,
    PowerSeries.derivative_C, PowerSeries.derivative_C, PowerSeries.derivative_X]
  simp only [smul_eq_mul]; ring

theorem derivative_fgInv : PowerSeries.derivative R W.fgInv =
    -PowerSeries.invOfUnit W.fgInvDenom (1 : Rˣ)
      + PowerSeries.X * (-PowerSeries.C W.a₁ - PowerSeries.C W.a₃ * PowerSeries.derivative R W.formalW)
        * PowerSeries.invOfUnit W.fgInvDenom (1 : Rˣ) ^ 2 := by
  rw [fgInv_eq, Derivation.leibniz, deriv_inv_of_mul_eq_one (fgInvDenom_mul_inv W), map_neg, PowerSeries.derivative_X,
    derivative_fgInvDenom]
  simp only [smul_eq_mul]; ring

theorem hasSubst_fgInv : PowerSeries.HasSubst W.fgInv := PowerSeries.HasSubst.of_constantCoeff_zero' W.constantCoeff_fgInv

theorem derivative_subst_fgInv (h : PowerSeries R) :
    PowerSeries.derivative R (PowerSeries.subst W.fgInv h) =
      PowerSeries.subst W.fgInv (PowerSeries.derivative R h) * PowerSeries.derivative R W.fgInv := by
  have e := MvPowerSeries.pderiv_subst () W.fgInv W.constantCoeff_fgInv h
  rw [pderiv_unit_eq_derivative, pderiv_unit_eq_derivative] at e
  exact e

theorem subst_fgInv_fgInvDenom : PowerSeries.subst W.fgInv W.fgInvDenom =
    1 - PowerSeries.C W.a₁ * W.fgInv - PowerSeries.C W.a₃ * PowerSeries.subst W.fgInv W.formalW := by
  rw [fgInvDenom_eq, ← PowerSeries.coe_substAlgHom (hasSubst_fgInv W)]
  simp only [map_sub, map_one, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_C,
    PowerSeries.subst_X (hasSubst_fgInv W)]
  rfl

theorem subst_fgInv_derivative_fgInv : PowerSeries.subst W.fgInv (PowerSeries.derivative R W.fgInv) =
    -PowerSeries.subst W.fgInv (PowerSeries.invOfUnit W.fgInvDenom (1 : Rˣ))
      + W.fgInv * (-PowerSeries.C W.a₁ - PowerSeries.C W.a₃ * PowerSeries.subst W.fgInv (PowerSeries.derivative R W.formalW))
        * PowerSeries.subst W.fgInv (PowerSeries.invOfUnit W.fgInvDenom (1 : Rˣ)) ^ 2 := by
  rw [derivative_fgInv, ← PowerSeries.coe_substAlgHom (hasSubst_fgInv W)]
  simp only [map_add, map_neg, map_mul, map_sub, map_pow, PowerSeries.coe_substAlgHom, PowerSeries.subst_C,
    PowerSeries.subst_X (hasSubst_fgInv W)]
  rfl

theorem subst_fgInv_inv_mul : PowerSeries.subst W.fgInv W.fgInvDenom *
    PowerSeries.subst W.fgInv (PowerSeries.invOfUnit W.fgInvDenom (1 : Rˣ)) = 1 := by
  rw [← PowerSeries.subst_mul (hasSubst_fgInv W), fgInvDenom_mul_inv, ← PowerSeries.coe_substAlgHom (hasSubst_fgInv W), map_one]

theorem q_relation :
    PowerSeries.subst W.fgInv (PowerSeries.derivative R W.formalW) * PowerSeries.derivative R W.fgInv * W.fgInvDenom
      + PowerSeries.subst W.fgInv W.formalW * PowerSeries.derivative R W.fgInvDenom
      = -PowerSeries.derivative R W.formalW := by
  have h := congrArg (PowerSeries.derivative R) W.subst_fgInv_formalW_mul_fgInvDenom
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_neg, derivative_subst_fgInv] at h
  linear_combination h

theorem chart_deriv :
    (1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₂ * PowerSeries.X ^ 2 - 2 * PowerSeries.C W.a₃ * W.formalW
      - 2 * PowerSeries.C W.a₄ * PowerSeries.X * W.formalW - 3 * PowerSeries.C W.a₆ * W.formalW ^ 2)
      * PowerSeries.derivative R W.formalW
    = 3 * PowerSeries.X ^ 2 + PowerSeries.C W.a₁ * W.formalW + 2 * PowerSeries.C W.a₂ * PowerSeries.X * W.formalW
      + PowerSeries.C W.a₄ * W.formalW ^ 2 := by
  have h := congrArg (PowerSeries.derivative R) W.formalW_eq
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_C, PowerSeries.derivative_X,
    smul_eq_mul, smul_zero, _root_.add_zero, mul_zero, _root_.zero_add, mul_one] at h
  linear_combination h

theorem isUnit_of_constantCoeff {f : PowerSeries R} {c : R} (hc : PowerSeries.constantCoeff f = c) (hu : IsUnit c) :
    IsUnit f := PowerSeries.isUnit_iff_constantCoeff.mpr (hc ▸ hu)

theorem constantCoeff_lam0 : PowerSeries.constantCoeff (lam0 W) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, lam0, PowerSeries.coeff_mk, _root_.zero_add, W.coeff_formalW_one]

end DW2KEY

open DW2KEY in
set_option maxHeartbeats 32000000 in
set_option maxRecDepth 4000 in
theorem solution
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    (W.formalW * (PowerSeries.C W.a₃ * W.formalW + PowerSeries.C W.a₁ * PowerSeries.X - 2)) = (W.formalW - PowerSeries.X * PowerSeries.derivative R W.formalW) * MvPowerSeries.subst ![(0 : PowerSeries R), PowerSeries.X]
        (MvPowerSeries.pderivLin 0 W.formalGroupLawFixed) := by
  have hw0 : W.formalW = PowerSeries.X * lam0 W := (X_mul_lam0 W).symm
  have hR4' : PowerSeries.X * mu W = lam0 W := X_mul_mu W
  have hR5' := chart_lam0 W
  have hdd' := fgInvDenom_mul_inv W
  have hDI' := Den0_mul_EDI W
  have hi' := fgInv_eq W
  have hBR' := W.subst_fgInv_formalW_mul_fgInvDenom
  have hdI' := subst_fgInv_inv_mul W
  have hdenI' := subst_fgInv_fgInvDenom W
  have hQ' := q_relation W
  have hR6' := chart_deriv W
  have hdfi := derivative_fgInv W
  have hL0 := constantCoeff_lam0 W
  rw [E_pderiv_formalGroupLawFixed, E_pderiv_fgZ3Fixed, E_pderiv_fgZ3NumFixed, E_fgZ3NumFixed, E_pderiv_fgZ3Denom,
    subst_fgInv_derivative_fgInv,
    show PowerSeries.C (2 * W.a₄) = 2 * PowerSeries.C W.a₄ by rw [map_mul, map_ofNat],
    show PowerSeries.C (3 * W.a₆) = 3 * PowerSeries.C W.a₆ by rw [map_mul, map_ofNat]]
  rw [hdfi, derivative_fgInvDenom] at hQ'
  unfold Den0 at hDI'

  set dinv : PowerSeries R := PowerSeries.invOfUnit W.fgInvDenom (1 : Rˣ) with hdinv
  set dinvI : PowerSeries R := PowerSeries.subst W.fgInv dinv with hdinvIdef
  set DEN_I : PowerSeries R := PowerSeries.subst W.fgInv W.fgInvDenom with hDENI
  rw [fgInvDenom_eq] at hdd' hBR' hQ'
  set WP : PowerSeries R := PowerSeries.derivative R W.formalW with hWP
  set Q : PowerSeries R := PowerSeries.subst W.fgInv WP with hQdef
  set wI : PowerSeries R := PowerSeries.subst W.fgInv W.formalW with hwIdef
  set DI : PowerSeries R := MvPowerSeries.subst (![(0 : PowerSeries R), PowerSeries.X] : Fin 2 → PowerSeries R)
    (MvPowerSeries.invOfUnit W.fgZ3Denom (1 : Rˣ)) with hDIdef
  set I : PowerSeries R := W.fgInv with hIdef
  set w : PowerSeries R := W.formalW with hwdef
  set T : PowerSeries R := PowerSeries.X with hT
  set L : PowerSeries R := lam0 W with hL
  set MU : PowerSeries R := mu W with hMU
  set A1 : PowerSeries R := PowerSeries.C W.a₁ with hA1
  set A2 : PowerSeries R := PowerSeries.C W.a₂ with hA2
  set A3 : PowerSeries R := PowerSeries.C W.a₃ with hA3
  set A4 : PowerSeries R := PowerSeries.C W.a₄ with hA4
  set A6 : PowerSeries R := PowerSeries.C W.a₆ with hA6
  have hwsub : w = T * L := hw0

  have hwI : wI = -w * dinv := by linear_combination dinv * hBR' - wI * hdd'
  have hdenI : DEN_I = dinv := by
    rw [hdenI', hwI, hi']
    linear_combination (-1 : PowerSeries R) * hdd'
  have hdinvI : dinvI = (1 - A1 * T - A3 * w) := by
    rw [hdenI] at hdI'
    linear_combination (1 - A1 * T - A3 * w) * hdI' - dinvI * hdd'

  have hS : -dinvI + I * (-A1 - A3 * Q) * dinvI ^ 2 = (-(1 - A1 * T - A3 * w) + T * (A1 + A3 * Q) * (1 - A1 * T - A3 * w)) := by
    rw [hdinvI, hi']
    linear_combination (-A1^2*T^2 - A1*A3*Q*T^2 - A1*A3*T*w + A1*T - A3^2*Q*T*w + A3*Q*T) * hdd'
  have hR7 : (T * (-A1 - A3 * WP) - (1 - A1 * T - A3 * w)) * Q = (w * (-A1 - A3 * WP) - WP * (1 - A1 * T - A3 * w)) := by
    linear_combination (1 - A1 * T - A3 * w) * hQ' - (-A1 - A3*WP) * hBR' - (A1^2*Q*T^2*dinv + A1*A3*Q*T^2*WP*dinv + A1*A3*Q*T*dinv*w - A1*Q*T*dinv + A3^2*Q*T*WP*dinv*w - A3*Q*T*WP*dinv - A3*Q*T*WP + A3*Q*w - Q) * hdd'
  have hR7L : (T * (-A1 - A3 * WP) - (1 - A1 * T - A3 * (T * L))) * Q = ((T * L) * (-A1 - A3 * WP) - WP * (1 - A1 * T - A3 * (T * L))) := by linear_combination hR7 - (A1 + A3*Q) * hwsub
  have hR6L : (1 - A1 * T - A2 * T ^ 2 - 2 * A3 * (T * L) - 2 * A4 * T * (T * L) - 3 * A6 * (T * L) ^ 2) * WP = (3 * T ^ 2 + A1 * (T * L) + 2 * A2 * T * (T * L) + A4 * (T * L) ^ 2) := by linear_combination hR6' - (-A1 - 2*A2*T - 2*A3*WP - A4*L*T - 2*A4*T*WP - A4*w - 3*A6*L*T*WP - 3*A6*WP*w) * hwsub

  have big : T * ((1 - A1 * T - A2 * T ^ 2 - 2 * A3 * (T * L) - 2 * A4 * T * (T * L) - 3 * A6 * (T * L) ^ 2) * ((T * (-A1 - A3 * WP) - (1 - A1 * T - A3 * (T * L))) * ((T * L - T * WP) * (-(1 - A1 * T - A3 * (T * L)) + T * (A1 + A3 * Q) * (1 - A1 * T - A3 * (T * L))) * (-(1 + A2 * L + A4 * L ^ 2 + A6 * L ^ 3) ^ 2 + (-(A1 * MU + 2 * A3 * L * MU - A2 * L - 2 * A4 * L ^ 2 - 3 * A6 * L ^ 3)) * (1 + A2 * L + A4 * L ^ 2 + A6 * L ^ 3) - (-(A1 * L + A3 * L ^ 2)) * ((A2 + 2 * A4 * L + 3 * A6 * L ^ 2) * MU)))))
      = T * ((1 - A1 * T - A2 * T ^ 2 - 2 * A3 * (T * L) - 2 * A4 * T * (T * L) - 3 * A6 * (T * L) ^ 2) * ((T * (-A1 - A3 * WP) - (1 - A1 * T - A3 * (T * L))) * ((1 + A2 * L + A4 * L ^ 2 + A6 * L ^ 3) ^ 2 * ((T * L) * (A3 * (T * L) + A1 * T - 2))))) := by
    linear_combination (A1^3*A3*A4*L^3*MU*T^5 - A1^3*A3*A4*L^2*MU*T^5*WP + 2*A1^3*A3*A6*L^4*MU*T^5 - 2*A1^3*A3*A6*L^3*MU*T^5*WP - A1^3*A3*L*MU*T^5 + A1^3*A3*MU*T^5*WP - A1^2*A2*A3^2*L^3*MU*T^5 + A1^2*A2*A3^2*L^2*MU*T^5*WP + A1^2*A2*A3*A4*L^4*T^5 + A1^2*A2*A3*A4*L^3*MU*T^6 - A1^2*A2*A3*A4*L^3*T^5*WP - A1^2*A2*A3*A4*L^2*MU*T^6*WP + 2*A1^2*A2*A3*A6*L^5*T^5 + 2*A1^2*A2*A3*A6*L^4*MU*T^6 - 2*A1^2*A2*A3*A6*L^4*T^5*WP - 2*A1^2*A2*A3*A6*L^3*MU*T^6*WP - A1^2*A2*A3*L^2*T^5 - A1^2*A2*A3*L*MU*T^6 + A1^2*A2*A3*L*T^5*WP + A1^2*A2*A3*MU*T^6*WP + 3*A1^2*A3^2*A4*L^4*MU*T^5 - 3*A1^2*A3^2*A4*L^3*MU*T^5*WP + 7*A1^2*A3^2*A6*L^5*MU*T^5 - 7*A1^2*A3^2*A6*L^4*MU*T^5*WP - 5*A1^2*A3^2*L^2*MU*T^5 + 5*A1^2*A3^2*L*MU*T^5*WP + A1^2*A3*A4^2*L^5*T^5 + 2*A1^2*A3*A4^2*L^4*MU*T^6 - A1^2*A3*A4^2*L^4*T^5*WP - 2*A1^2*A3*A4^2*L^3*MU*T^6*WP + 3*A1^2*A3*A4*A6*L^6*T^5 + 7*A1^2*A3*A4*A6*L^5*MU*T^6 - 3*A1^2*A3*A4*A6*L^5*T^5*WP - 7*A1^2*A3*A4*A6*L^4*MU*T^6*WP - 2*A1^2*A3*A4*L^3*MU*T^4 - 2*A1^2*A3*A4*L^2*MU*T^6 + 2*A1^2*A3*A4*L^2*MU*T^4*WP + 2*A1^2*A3*A4*L*MU*T^6*WP + 2*A1^2*A3*A6^2*L^7*T^5 + 6*A1^2*A3*A6^2*L^6*MU*T^6 - 2*A1^2*A3*A6^2*L^6*T^5*WP - 6*A1^2*A3*A6^2*L^5*MU*T^6*WP - 4*A1^2*A3*A6*L^4*MU*T^4 + A1^2*A3*A6*L^4*T^5 - 3*A1^2*A3*A6*L^3*MU*T^6 + 4*A1^2*A3*A6*L^3*MU*T^4*WP - A1^2*A3*A6*L^3*T^5*WP + 3*A1^2*A3*A6*L^2*MU*T^6*WP + 2*A1^2*A3*L*MU*T^4 - A1^2*A3*L*T^5 - 2*A1^2*A3*MU*T^4*WP + A1^2*A3*T^5*WP - A1*A2^2*A3^2*L^3*MU*T^6 + A1*A2^2*A3^2*L^2*MU*T^6*WP + A1*A2^2*A3*A4*L^4*T^6 - A1*A2^2*A3*A4*L^3*T^6*WP + 2*A1*A2^2*A3*A6*L^5*T^6 - 2*A1*A2^2*A3*A6*L^4*T^6*WP - A1*A2^2*A3*L^2*T^6 + A1*A2^2*A3*L*T^6*WP - 3*A1*A2*A3^3*L^4*MU*T^5 + 3*A1*A2*A3^3*L^3*MU*T^5*WP + 3*A1*A2*A3^2*A4*L^5*T^5 - A1*A2*A3^2*A4*L^4*MU*T^6 - 3*A1*A2*A3^2*A4*L^4*T^5*WP + A1*A2*A3^2*A4*L^3*MU*T^6*WP + 6*A1*A2*A3^2*A6*L^6*T^5 - 6*A1*A2*A3^2*A6*L^5*T^5*WP + 2*A1*A2*A3^2*L^3*MU*T^4 - 3*A1*A2*A3^2*L^3*T^5 - 3*A1*A2*A3^2*L^2*MU*T^6 - 2*A1*A2*A3^2*L^2*MU*T^4*WP + 3*A1*A2*A3^2*L^2*T^5*WP + 3*A1*A2*A3^2*L*MU*T^6*WP + 3*A1*A2*A3*A4^2*L^5*T^6 - 3*A1*A2*A3*A4^2*L^4*T^6*WP + 10*A1*A2*A3*A4*A6*L^6*T^6 - 10*A1*A2*A3*A4*A6*L^5*T^6*WP - 2*A1*A2*A3*A4*L^4*T^4 - A1*A2*A3*A4*L^3*MU*T^5 - 2*A1*A2*A3*A4*L^3*T^6 + 2*A1*A2*A3*A4*L^3*T^4*WP + A1*A2*A3*A4*L^2*MU*T^5*WP + 2*A1*A2*A3*A4*L^2*T^6*WP + 8*A1*A2*A3*A6^2*L^7*T^6 - 8*A1*A2*A3*A6^2*L^6*T^6*WP - 4*A1*A2*A3*A6*L^5*T^4 - 2*A1*A2*A3*A6*L^4*MU*T^5 - 2*A1*A2*A3*A6*L^4*T^6 + 4*A1*A2*A3*A6*L^4*T^4*WP + 2*A1*A2*A3*A6*L^3*MU*T^5*WP + 2*A1*A2*A3*A6*L^3*T^6*WP + 2*A1*A2*A3*L^2*T^4 + A1*A2*A3*L*MU*T^5 - A1*A2*A3*L*T^6 - 2*A1*A2*A3*L*T^4*WP - A1*A2*A3*MU*T^5*WP + A1*A2*A3*T^6*WP + 2*A1*A3^3*A4*L^5*MU*T^5 - 2*A1*A3^3*A4*L^4*MU*T^5*WP + 7*A1*A3^3*A6*L^6*MU*T^5 - 7*A1*A3^3*A6*L^5*MU*T^5*WP - 8*A1*A3^3*L^3*MU*T^5 + 8*A1*A3^3*L^2*MU*T^5*WP + 3*A1*A3^2*A4^2*L^6*T^5 + 2*A1*A3^2*A4^2*L^5*MU*T^6 - 3*A1*A3^2*A4^2*L^5*T^5*WP - 2*A1*A3^2*A4^2*L^4*MU*T^6*WP + 9*A1*A3^2*A4*A6*L^7*T^5 + 9*A1*A3^2*A4*A6*L^6*MU*T^6 - 9*A1*A3^2*A4*A6*L^6*T^5*WP - 9*A1*A3^2*A4*A6*L^5*MU*T^6*WP - 3*A1*A3^2*A4*L^4*MU*T^4 - 6*A1*A3^2*A4*L^3*MU*T^6 + 3*A1*A3^2*A4*L^3*MU*T^4*WP + 6*A1*A3^2*A4*L^2*MU*T^6*WP + 6*A1*A3^2*A6^2*L^8*T^5 + 9*A1*A3^2*A6^2*L^7*MU*T^6 - 6*A1*A3^2*A6^2*L^7*T^5*WP - 9*A1*A3^2*A6^2*L^6*MU*T^6*WP - 8*A1*A3^2*A6*L^5*MU*T^4 + 3*A1*A3^2*A6*L^5*T^5 - 9*A1*A3^2*A6*L^4*MU*T^6 + 8*A1*A3^2*A6*L^4*MU*T^4*WP - 3*A1*A3^2*A6*L^4*T^5*WP + 9*A1*A3^2*A6*L^3*MU*T^6*WP + 7*A1*A3^2*L^2*MU*T^4 - 3*A1*A3^2*L^2*T^5 - 7*A1*A3^2*L*MU*T^4*WP + 3*A1*A3^2*L*T^5*WP + 2*A1*A3*A4^3*L^6*T^6 - 2*A1*A3*A4^3*L^5*T^6*WP + 9*A1*A3*A4^2*A6*L^7*T^6 - 9*A1*A3*A4^2*A6*L^6*T^6*WP - 2*A1*A3*A4^2*L^5*T^4 - 2*A1*A3*A4^2*L^4*MU*T^5 + 2*A1*A3*A4^2*L^4*T^4*WP + 2*A1*A3*A4^2*L^3*MU*T^5*WP + 13*A1*A3*A4*A6^2*L^8*T^6 - 13*A1*A3*A4*A6^2*L^7*T^6*WP - 6*A1*A3*A4*A6*L^6*T^4 - 7*A1*A3*A4*A6*L^5*MU*T^5 + 2*A1*A3*A4*A6*L^5*T^6 + 6*A1*A3*A4*A6*L^5*T^4*WP + 7*A1*A3*A4*A6*L^4*MU*T^5*WP - 2*A1*A3*A4*A6*L^4*T^6*WP + A1*A3*A4*L^3*MU*T^3 + 2*A1*A3*A4*L^2*MU*T^5 - A1*A3*A4*L^2*MU*T^3*WP - 2*A1*A3*A4*L^2*T^6 - 2*A1*A3*A4*L*MU*T^5*WP + 2*A1*A3*A4*L*T^6*WP + 6*A1*A3*A6^3*L^9*T^6 - 6*A1*A3*A6^3*L^8*T^6*WP - 4*A1*A3*A6^2*L^7*T^4 - 6*A1*A3*A6^2*L^6*MU*T^5 + 3*A1*A3*A6^2*L^6*T^6 + 4*A1*A3*A6^2*L^6*T^4*WP + 6*A1*A3*A6^2*L^5*MU*T^5*WP - 3*A1*A3*A6^2*L^5*T^6*WP + 2*A1*A3*A6*L^4*MU*T^3 - 2*A1*A3*A6*L^4*T^4 + 3*A1*A3*A6*L^3*MU*T^5 - 2*A1*A3*A6*L^3*MU*T^3*WP - 3*A1*A3*A6*L^3*T^6 + 2*A1*A3*A6*L^3*T^4*WP - 3*A1*A3*A6*L^2*MU*T^5*WP + 3*A1*A3*A6*L^2*T^6*WP - A1*A3*L*MU*T^3 + 2*A1*A3*L*T^4 + A1*A3*MU*T^3*WP - 2*A1*A3*T^4*WP - A2^2*A3^3*L^4*MU*T^6 + A2^2*A3^3*L^3*MU*T^6*WP + A2^2*A3^2*A4*L^5*T^6 - A2^2*A3^2*A4*L^4*T^6*WP + 2*A2^2*A3^2*A6*L^6*T^6 - 2*A2^2*A3^2*A6*L^5*T^6*WP + A2^2*A3^2*L^3*MU*T^5 - A2^2*A3^2*L^3*T^6 - A2^2*A3^2*L^2*MU*T^5*WP + A2^2*A3^2*L^2*T^6*WP - A2^2*A3*A4*L^4*T^5 + A2^2*A3*A4*L^3*T^5*WP - 2*A2^2*A3*A6*L^5*T^5 + 2*A2^2*A3*A6*L^4*T^5*WP + A2^2*A3*L^2*T^5 - A2^2*A3*L*T^5*WP - 2*A2*A3^4*L^5*MU*T^5 + 2*A2*A3^4*L^4*MU*T^5*WP + 2*A2*A3^3*A4*L^6*T^5 - 2*A2*A3^3*A4*L^5*MU*T^6 - 2*A2*A3^3*A4*L^5*T^5*WP + 2*A2*A3^3*A4*L^4*MU*T^6*WP + 4*A2*A3^3*A6*L^7*T^5 - 2*A2*A3^3*A6*L^6*MU*T^6 - 4*A2*A3^3*A6*L^6*T^5*WP + 2*A2*A3^3*A6*L^5*MU*T^6*WP + 3*A2*A3^3*L^4*MU*T^4 - 2*A2*A3^3*L^4*T^5 - 2*A2*A3^3*L^3*MU*T^6 - 3*A2*A3^3*L^3*MU*T^4*WP + 2*A2*A3^3*L^3*T^5*WP + 2*A2*A3^3*L^2*MU*T^6*WP + 3*A2*A3^2*A4^2*L^6*T^6 - 3*A2*A3^2*A4^2*L^5*T^6*WP + 10*A2*A3^2*A4*A6*L^7*T^6 - 10*A2*A3^2*A4*A6*L^6*T^6*WP - 3*A2*A3^2*A4*L^5*T^4 + 2*A2*A3^2*A4*L^4*MU*T^5 - 2*A2*A3^2*A4*L^4*T^6 + 3*A2*A3^2*A4*L^4*T^4*WP - 2*A2*A3^2*A4*L^3*MU*T^5*WP + 2*A2*A3^2*A4*L^3*T^6*WP + 8*A2*A3^2*A6^2*L^8*T^6 - 8*A2*A3^2*A6^2*L^7*T^6*WP - 6*A2*A3^2*A6*L^6*T^4 + 2*A2*A3^2*A6*L^5*MU*T^5 - 2*A2*A3^2*A6*L^5*T^6 + 6*A2*A3^2*A6*L^5*T^4*WP - 2*A2*A3^2*A6*L^4*MU*T^5*WP + 2*A2*A3^2*A6*L^4*T^6*WP - A2*A3^2*L^3*MU*T^3 + 3*A2*A3^2*L^3*T^4 + 2*A2*A3^2*L^2*MU*T^5 + A2*A3^2*L^2*MU*T^3*WP - A2*A3^2*L^2*T^6 - 3*A2*A3^2*L^2*T^4*WP - 2*A2*A3^2*L*MU*T^5*WP + A2*A3^2*L*T^6*WP - 3*A2*A3*A4^2*L^5*T^5 + 3*A2*A3*A4^2*L^4*T^5*WP - 10*A2*A3*A4*A6*L^6*T^5 + 10*A2*A3*A4*A6*L^5*T^5*WP + A2*A3*A4*L^4*T^3 + 2*A2*A3*A4*L^3*T^5 - A2*A3*A4*L^3*T^3*WP - 2*A2*A3*A4*L^2*T^5*WP - 8*A2*A3*A6^2*L^7*T^5 + 8*A2*A3*A6^2*L^6*T^5*WP + 2*A2*A3*A6*L^5*T^3 + 2*A2*A3*A6*L^4*T^5 - 2*A2*A3*A6*L^4*T^3*WP - 2*A2*A3*A6*L^3*T^5*WP - A2*A3*L^2*T^3 + A2*A3*L*T^5 + A2*A3*L*T^3*WP - A2*A3*T^5*WP + 2*A3^4*A6*L^7*MU*T^5 - 2*A3^4*A6*L^6*MU*T^5*WP - 4*A3^4*L^4*MU*T^5 + 4*A3^4*L^3*MU*T^5*WP + 2*A3^3*A4^2*L^7*T^5 - 2*A3^3*A4^2*L^6*T^5*WP + 6*A3^3*A4*A6*L^8*T^5 + 2*A3^3*A4*A6*L^7*MU*T^6 - 6*A3^3*A4*A6*L^7*T^5*WP - 2*A3^3*A4*A6*L^6*MU*T^6*WP - 4*A3^3*A4*L^4*MU*T^6 + 4*A3^3*A4*L^3*MU*T^6*WP + 4*A3^3*A6^2*L^9*T^5 + 3*A3^3*A6^2*L^8*MU*T^6 - 4*A3^3*A6^2*L^8*T^5*WP - 3*A3^3*A6^2*L^7*MU*T^6*WP - 3*A3^3*A6*L^6*MU*T^4 + 2*A3^3*A6*L^6*T^5 - 6*A3^3*A6*L^5*MU*T^6 + 3*A3^3*A6*L^5*MU*T^4*WP - 2*A3^3*A6*L^5*T^5*WP + 6*A3^3*A6*L^4*MU*T^6*WP + 6*A3^3*L^3*MU*T^4 - 2*A3^3*L^3*T^5 - 6*A3^3*L^2*MU*T^4*WP + 2*A3^3*L^2*T^5*WP + 2*A3^2*A4^3*L^7*T^6 - 2*A3^2*A4^3*L^6*T^6*WP + 9*A3^2*A4^2*A6*L^8*T^6 - 9*A3^2*A4^2*A6*L^7*T^6*WP - 3*A3^2*A4^2*L^6*T^4 + 3*A3^2*A4^2*L^5*T^4*WP + 13*A3^2*A4*A6^2*L^9*T^6 - 13*A3^2*A4*A6^2*L^8*T^6*WP - 9*A3^2*A4*A6*L^7*T^4 - 2*A3^2*A4*A6*L^6*MU*T^5 + 2*A3^2*A4*A6*L^6*T^6 + 9*A3^2*A4*A6*L^6*T^4*WP + 2*A3^2*A4*A6*L^5*MU*T^5*WP - 2*A3^2*A4*A6*L^5*T^6*WP + 4*A3^2*A4*L^3*MU*T^5 - 2*A3^2*A4*L^3*T^6 - 4*A3^2*A4*L^2*MU*T^5*WP + 2*A3^2*A4*L^2*T^6*WP + 6*A3^2*A6^3*L^10*T^6 - 6*A3^2*A6^3*L^9*T^6*WP - 6*A3^2*A6^2*L^8*T^4 - 3*A3^2*A6^2*L^7*MU*T^5 + 3*A3^2*A6^2*L^7*T^6 + 6*A3^2*A6^2*L^7*T^4*WP + 3*A3^2*A6^2*L^6*MU*T^5*WP - 3*A3^2*A6^2*L^6*T^6*WP + A3^2*A6*L^5*MU*T^3 - 3*A3^2*A6*L^5*T^4 + 6*A3^2*A6*L^4*MU*T^5 - A3^2*A6*L^4*MU*T^3*WP - 3*A3^2*A6*L^4*T^6 + 3*A3^2*A6*L^4*T^4*WP - 6*A3^2*A6*L^3*MU*T^5*WP + 3*A3^2*A6*L^3*T^6*WP - 2*A3^2*L^2*MU*T^3 + 3*A3^2*L^2*T^4 + 2*A3^2*L*MU*T^3*WP - 3*A3^2*L*T^4*WP - 2*A3*A4^3*L^6*T^5 + 2*A3*A4^3*L^5*T^5*WP - 9*A3*A4^2*A6*L^7*T^5 + 9*A3*A4^2*A6*L^6*T^5*WP + A3*A4^2*L^5*T^3 - A3*A4^2*L^4*T^3*WP - 13*A3*A4*A6^2*L^8*T^5 + 13*A3*A4*A6^2*L^7*T^5*WP + 3*A3*A4*A6*L^6*T^3 - 2*A3*A4*A6*L^5*T^5 - 3*A3*A4*A6*L^5*T^3*WP + 2*A3*A4*A6*L^4*T^5*WP + 2*A3*A4*L^2*T^5 - 2*A3*A4*L*T^5*WP - 6*A3*A6^3*L^9*T^5 + 6*A3*A6^3*L^8*T^5*WP + 2*A3*A6^2*L^7*T^3 - 3*A3*A6^2*L^6*T^5 - 2*A3*A6^2*L^6*T^3*WP + 3*A3*A6^2*L^5*T^5*WP + A3*A6*L^4*T^3 + 3*A3*A6*L^3*T^5 - A3*A6*L^3*T^3*WP - 3*A3*A6*L^2*T^5*WP - A3*L*T^3 + A3*T^3*WP) * hR7L + (-A1^3*A4*L^2*MU*T^4 - 2*A1^3*A6*L^3*MU*T^4 + A1^3*MU*T^4 + A1^2*A2*A3*L^2*MU*T^4 - A1^2*A2*A4*L^3*T^4 - 2*A1^2*A2*A6*L^4*T^4 + A1^2*A2*L*T^4 - 2*A1^2*A3*A4*L^3*MU*T^4 - 5*A1^2*A3*A6*L^4*MU*T^4 + 4*A1^2*A3*L*MU*T^4 - A1^2*A4^2*L^4*T^4 - 3*A1^2*A4*A6*L^5*T^4 + 2*A1^2*A4*L^2*MU*T^3 - 2*A1^2*A6^2*L^6*T^4 + 4*A1^2*A6*L^3*MU*T^3 - A1^2*A6*L^3*T^4 - 2*A1^2*MU*T^3 + A1^2*T^4 + A1*A2^2*A3*L^3*T^4 + 2*A1*A2*A3^2*L^3*MU*T^4 - 2*A1*A2*A3*A6*L^5*T^4 - 2*A1*A2*A3*L^2*MU*T^3 + 4*A1*A2*A3*L^2*T^4 + 2*A1*A2*A4*L^3*T^3 + 4*A1*A2*A6*L^4*T^3 - 2*A1*A2*L*T^3 - A1*A3^2*A4*L^4*MU*T^4 - 4*A1*A3^2*A6*L^5*MU*T^4 + 5*A1*A3^2*L^2*MU*T^4 - A1*A3*A4^2*L^5*T^4 - 4*A1*A3*A4*A6*L^6*T^4 + 2*A1*A3*A4*L^3*MU*T^3 + 2*A1*A3*A4*L^3*T^4 - 3*A1*A3*A6^2*L^7*T^4 + 6*A1*A3*A6*L^4*MU*T^3 - 6*A1*A3*L*MU*T^3 + 3*A1*A3*L*T^4 + 2*A1*A4^2*L^4*T^3 + 6*A1*A4*A6*L^5*T^3 - A1*A4*L^2*MU*T^2 + 4*A1*A6^2*L^6*T^3 - 2*A1*A6*L^3*MU*T^2 + 2*A1*A6*L^3*T^3 + A1*MU*T^2 - 2*A1*T^3 + A2^2*A3^2*L^4*T^4 - 2*A2^2*A3*L^3*T^3 + A2*A3^3*L^4*MU*T^4 + A2*A3^2*A4*L^5*T^4 - 2*A2*A3^2*L^3*MU*T^3 + 3*A2*A3^2*L^3*T^4 - 2*A2*A3*A4*L^4*T^3 + A2*A3*L^2*MU*T^2 - 6*A2*A3*L^2*T^3 - A2*A4*L^3*T^2 - 2*A2*A6*L^4*T^2 + A2*L*T^2 - A3^3*A6*L^6*MU*T^4 + 2*A3^3*L^3*MU*T^4 - A3^2*A4*A6*L^7*T^4 + 2*A3^2*A4*L^4*T^4 - A3^2*A6^2*L^8*T^4 + 2*A3^2*A6*L^5*MU*T^3 + A3^2*A6*L^5*T^4 - 4*A3^2*L^2*MU*T^3 + 2*A3^2*L^2*T^4 + 2*A3*A4*A6*L^6*T^3 - 4*A3*A4*L^3*T^3 + 2*A3*A6^2*L^7*T^3 - A3*A6*L^4*MU*T^2 - 2*A3*A6*L^4*T^3 + 2*A3*L*MU*T^2 - 4*A3*L*T^3 - A4^2*L^4*T^2 - 3*A4*A6*L^5*T^2 - 2*A6^2*L^6*T^2 - A6*L^3*T^2 + T^2) * hR6L + (-2*A1^4*A4*L^3*T^4 - 4*A1^4*A6*L^4*T^4 + 2*A1^4*L*T^4 + 2*A1^3*A2*A3*L^3*T^4 - 3*A1^3*A2*A4*L^3*T^5 - 6*A1^3*A2*A6*L^4*T^5 + 3*A1^3*A2*L*T^5 - 6*A1^3*A3*A4*L^4*T^4 - 14*A1^3*A3*A6*L^5*T^4 + 10*A1^3*A3*L^2*T^4 - 3*A1^3*A4^2*L^4*T^5 - 9*A1^3*A4*A6*L^5*T^5 + 5*A1^3*A4*L^3*T^3 - 6*A1^3*A6^2*L^6*T^5 + 10*A1^3*A6*L^4*T^3 - 3*A1^3*A6*L^3*T^5 - 5*A1^3*L*T^3 + 3*A1^3*T^5 + 3*A1^2*A2^2*A3*L^3*T^5 + 6*A1^2*A2*A3^2*L^4*T^4 - 3*A1^2*A2*A3*A4*L^4*T^5 - 12*A1^2*A2*A3*A6*L^5*T^5 - 5*A1^2*A2*A3*L^3*T^3 + 15*A1^2*A2*A3*L^2*T^5 + 6*A1^2*A2*A4*L^3*T^4 + 12*A1^2*A2*A6*L^4*T^4 - 6*A1^2*A2*L*T^4 - 6*A1^2*A3^2*A4*L^5*T^4 - 18*A1^2*A3^2*A6*L^6*T^4 + 18*A1^2*A3^2*L^3*T^4 - 6*A1^2*A3*A4^2*L^5*T^5 - 21*A1^2*A3*A4*A6*L^6*T^5 + 10*A1^2*A3*A4*L^4*T^3 + 6*A1^2*A3*A4*L^3*T^5 - 15*A1^2*A3*A6^2*L^7*T^5 + 25*A1^2*A3*A6*L^5*T^3 - 3*A1^2*A3*A6*L^4*T^5 - 20*A1^2*A3*L^2*T^3 + 12*A1^2*A3*L*T^5 + 6*A1^2*A4^2*L^4*T^4 + 18*A1^2*A4*A6*L^5*T^4 - 4*A1^2*A4*L^3*T^2 + 12*A1^2*A6^2*L^6*T^4 - 8*A1^2*A6*L^4*T^2 + 6*A1^2*A6*L^3*T^4 + 4*A1^2*L*T^2 - 6*A1^2*T^4 + 6*A1*A2^2*A3^2*L^4*T^5 - 6*A1*A2^2*A3*L^3*T^4 + 6*A1*A2*A3^3*L^5*T^4 + 3*A1*A2*A3^2*A4*L^5*T^5 - 6*A1*A2*A3^2*A6*L^6*T^5 - 10*A1*A2*A3^2*L^4*T^3 + 21*A1*A2*A3^2*L^3*T^5 + 12*A1*A2*A3*A6*L^5*T^4 + 4*A1*A2*A3*L^3*T^2 - 24*A1*A2*A3*L^2*T^4 - 3*A1*A2*A4*L^3*T^3 - 6*A1*A2*A6*L^4*T^3 + 3*A1*A2*L*T^3 - 2*A1*A3^3*A4*L^6*T^4 - 10*A1*A3^3*A6*L^7*T^4 + 14*A1*A3^3*L^4*T^4 - 3*A1*A3^2*A4^2*L^6*T^5 - 15*A1*A3^2*A4*A6*L^7*T^5 + 5*A1*A3^2*A4*L^5*T^3 + 12*A1*A3^2*A4*L^4*T^5 - 12*A1*A3^2*A6^2*L^8*T^5 + 20*A1*A3^2*A6*L^6*T^3 + 3*A1*A3^2*A6*L^5*T^5 - 25*A1*A3^2*L^3*T^3 + 15*A1*A3^2*L^2*T^5 + 6*A1*A3*A4^2*L^5*T^4 + 24*A1*A3*A4*A6*L^6*T^4 - 4*A1*A3*A4*L^4*T^2 - 12*A1*A3*A4*L^3*T^4 + 18*A1*A3*A6^2*L^7*T^4 - 12*A1*A3*A6*L^5*T^2 + 12*A1*A3*L^2*T^2 - 18*A1*A3*L*T^4 - 3*A1*A4^2*L^4*T^3 - 9*A1*A4*A6*L^5*T^3 + A1*A4*L^3*T - 6*A1*A6^2*L^6*T^3 + 2*A1*A6*L^4*T - 3*A1*A6*L^3*T^3 - A1*L*T + 3*A1*T^3 + 3*A2^2*A3^3*L^5*T^5 - 6*A2^2*A3^2*L^4*T^4 + 3*A2^2*A3*L^3*T^3 + 2*A2*A3^4*L^6*T^4 + 3*A2*A3^3*A4*L^6*T^5 - 5*A2*A3^3*L^5*T^3 + 9*A2*A3^3*L^4*T^5 - 6*A2*A3^2*A4*L^5*T^4 + 4*A2*A3^2*L^4*T^2 - 18*A2*A3^2*L^3*T^4 + 3*A2*A3*A4*L^4*T^3 - A2*A3*L^3*T + 9*A2*A3*L^2*T^3 - 2*A3^4*A6*L^8*T^4 + 4*A3^4*L^5*T^4 - 3*A3^3*A4*A6*L^8*T^5 + 6*A3^3*A4*L^5*T^5 - 3*A3^3*A6^2*L^9*T^5 + 5*A3^3*A6*L^7*T^3 + 3*A3^3*A6*L^6*T^5 - 10*A3^3*L^4*T^3 + 6*A3^3*L^3*T^5 + 6*A3^2*A4*A6*L^7*T^4 - 12*A3^2*A4*L^4*T^4 + 6*A3^2*A6^2*L^8*T^4 - 4*A3^2*A6*L^6*T^2 - 6*A3^2*A6*L^5*T^4 + 8*A3^2*L^3*T^2 - 12*A3^2*L^2*T^4 - 3*A3*A4*A6*L^6*T^3 + 6*A3*A4*L^3*T^3 - 3*A3*A6^2*L^7*T^3 + A3*A6*L^5*T + 3*A3*A6*L^4*T^3 - 2*A3*L^2*T + 6*A3*L*T^3) * hR4' + (2*A1^3*A4*L^3*T^3 + 4*A1^3*A6*L^4*T^3 - 2*A1^3*L*T^3 - 2*A1^2*A2*A3*L^3*T^3 + 3*A1^2*A2*A4*L^3*T^4 + 6*A1^2*A2*A6*L^4*T^4 - 3*A1^2*A2*L*T^4 + 4*A1^2*A3*A4*L^4*T^3 + 10*A1^2*A3*A6*L^5*T^3 - 8*A1^2*A3*L^2*T^3 + 3*A1^2*A4^2*L^4*T^4 + 9*A1^2*A4*A6*L^5*T^4 - 3*A1^2*A4*L^3*T^2 + 6*A1^2*A6^2*L^6*T^4 - 6*A1^2*A6*L^4*T^2 + 3*A1^2*A6*L^3*T^4 + 3*A1^2*L*T^2 - 3*A1^2*T^4 - 3*A1*A2^2*A3*L^3*T^4 + A1*A2^2*L^2*T^3 - 4*A1*A2*A3^2*L^4*T^3 + 6*A1*A2*A3*A6*L^5*T^4 + 3*A1*A2*A3*L^3*T^2 - 12*A1*A2*A3*L^2*T^4 - 3*A1*A2*A4*L^3*T^3 - 8*A1*A2*A6*L^4*T^3 + 7*A1*A2*L*T^3 + 2*A1*A3^2*A4*L^5*T^3 + 8*A1*A3^2*A6*L^6*T^3 - 10*A1*A3^2*L^3*T^3 + 3*A1*A3*A4^2*L^5*T^4 + 12*A1*A3*A4*A6*L^6*T^4 - 3*A1*A3*A4*L^4*T^2 - 6*A1*A3*A4*L^3*T^4 + 9*A1*A3*A6^2*L^7*T^4 - 9*A1*A3*A6*L^5*T^2 + 9*A1*A3*L^2*T^2 - 9*A1*A3*L*T^4 - 4*A1*A4^2*L^4*T^3 - 13*A1*A4*A6*L^5*T^3 + A1*A4*L^3*T + 2*A1*A4*L^2*T^3 - 9*A1*A6^2*L^6*T^3 + 2*A1*A6*L^4*T - 3*A1*A6*L^3*T^3 - A1*L*T + 6*A1*T^3 - 3*A2^2*A3^2*L^4*T^4 + 7*A2^2*A3*L^3*T^3 - 2*A2^2*L^2*T^2 - 2*A2*A3^3*L^5*T^3 - 3*A2*A3^2*A4*L^5*T^4 + 3*A2*A3^2*L^4*T^2 - 9*A2*A3^2*L^3*T^4 + 9*A2*A3*A4*L^4*T^3 + 4*A2*A3*A6*L^5*T^3 - A2*A3*L^3*T + 19*A2*A3*L^2*T^3 - 3*A2*A4*L^3*T^2 - 2*A2*A6*L^4*T^2 - 5*A2*L*T^2 + 2*A3^3*A6*L^7*T^3 - 4*A3^3*L^4*T^3 + 3*A3^2*A4*A6*L^7*T^4 - 6*A3^2*A4*L^4*T^4 + 3*A3^2*A6^2*L^8*T^4 - 3*A3^2*A6*L^6*T^2 - 3*A3^2*A6*L^5*T^4 + 6*A3^2*L^3*T^2 - 6*A3^2*L^2*T^4 + 2*A3*A4^2*L^5*T^3 - A3*A4*A6*L^6*T^3 + 14*A3*A4*L^3*T^3 - 3*A3*A6^2*L^7*T^3 + A3*A6*L^5*T + 9*A3*A6*L^4*T^3 - 2*A3*L^2*T + 12*A3*L*T^3 - A4^2*L^4*T^2 - A4*A6*L^5*T^2 - 4*A4*L^2*T^2 - 3*A6*L^3*T^2 - 3*T^2) * hR5'
  have hcp : IsUnit (1 - A1 * T - A2 * T ^ 2 - 2 * A3 * (T * L) - 2 * A4 * T * (T * L) - 3 * A6 * (T * L) ^ 2) := by
    apply isUnit_of_constantCoeff (c := 1) _ isUnit_one
    simp [hT, hL, hA1, hA2, hA3, hA4, hA6, hL0, PowerSeries.constantCoeff_X]
  have hα : IsUnit (T * (-A1 - A3 * WP) - (1 - A1 * T - A3 * (T * L))) := by
    apply isUnit_of_constantCoeff (c := -1) _ (isUnit_one.neg)
    simp [hT, hL, hA1, hA3, hL0, PowerSeries.constantCoeff_X]
  have hDen0 : IsUnit ((1 + A2 * L + A4 * L ^ 2 + A6 * L ^ 3) ^ 2) := by
    apply IsUnit.pow
    apply isUnit_of_constantCoeff (c := 1) _ isUnit_one
    simp [hA2, hA4, hA6, hL0]
  have h5 : (T * L - T * WP) * (-(1 - A1 * T - A3 * (T * L)) + T * (A1 + A3 * Q) * (1 - A1 * T - A3 * (T * L))) * (-(1 + A2 * L + A4 * L ^ 2 + A6 * L ^ 3) ^ 2 + (-(A1 * MU + 2 * A3 * L * MU - A2 * L - 2 * A4 * L ^ 2 - 3 * A6 * L ^ 3)) * (1 + A2 * L + A4 * L ^ 2 + A6 * L ^ 3) - (-(A1 * L + A3 * L ^ 2)) * ((A2 + 2 * A4 * L + 3 * A6 * L ^ 2) * MU)) = (1 + A2 * L + A4 * L ^ 2 + A6 * L ^ 3) ^ 2 * ((T * L) * (A3 * (T * L) + A1 * T - 2)) :=
    hα.mul_left_cancel (hcp.mul_left_cancel (PowerSeries.X_mul_cancel big))
  have hB : (1 + A2 * L + A4 * L ^ 2 + A6 * L ^ 3) ^ 2 * (-1 + (-(A1 * MU + 2 * A3 * L * MU - A2 * L - 2 * A4 * L ^ 2 - 3 * A6 * L ^ 3)) * DI - (-(A1 * L + A3 * L ^ 2)) * ((A2 + 2 * A4 * L + 3 * A6 * L ^ 2) * MU) * DI ^ 2) = (-(1 + A2 * L + A4 * L ^ 2 + A6 * L ^ 3) ^ 2 + (-(A1 * MU + 2 * A3 * L * MU - A2 * L - 2 * A4 * L ^ 2 - 3 * A6 * L ^ 3)) * (1 + A2 * L + A4 * L ^ 2 + A6 * L ^ 3) - (-(A1 * L + A3 * L ^ 2)) * ((A2 + 2 * A4 * L + 3 * A6 * L ^ 2) * MU)) := by
    linear_combination (A1*A2^2*DI*L^2*MU + 3*A1*A2*A4*DI*L^3*MU + 4*A1*A2*A6*DI*L^4*MU + A1*A2*DI*L*MU + 2*A1*A4^2*DI*L^4*MU + 5*A1*A4*A6*DI*L^5*MU + 2*A1*A4*DI*L^2*MU + A1*A4*L^2*MU + 3*A1*A6^2*DI*L^6*MU + 3*A1*A6*DI*L^3*MU + 2*A1*A6*L^3*MU - A1*MU + A2^2*A3*DI*L^3*MU + A2^2*L^2 + 3*A2*A3*A4*DI*L^4*MU + 4*A2*A3*A6*DI*L^5*MU + A2*A3*DI*L^2*MU - A2*A3*L^2*MU + 3*A2*A4*L^3 + 4*A2*A6*L^4 + A2*L + 2*A3*A4^2*DI*L^5*MU + 5*A3*A4*A6*DI*L^6*MU + 2*A3*A4*DI*L^3*MU + 3*A3*A6^2*DI*L^7*MU + 3*A3*A6*DI*L^4*MU + A3*A6*L^4*MU - 2*A3*L*MU + 2*A4^2*L^4 + 5*A4*A6*L^5 + 2*A4*L^2 + 3*A6^2*L^6 + 3*A6*L^3) * hDI'
  rw [hS]
  refine hDen0.mul_left_cancel ?_
  linear_combination (-1 : PowerSeries R) * h5 - ((w - T * WP) * (-(1 - A1 * T - A3 * w) + T * (A1 + A3 * Q) * (1 - A1 * T - A3 * w))) * hB + (A1^3*A4*L^2*MU*T^2 + 2*A1^3*A6*L^3*MU*T^2 - A1^3*MU*T^2 - A1^2*A2*A3*L^2*MU*T^2 + A1^2*A2*A4*L^3*T^2 + 2*A1^2*A2*A6*L^4*T^2 - A1^2*A2*L*T^2 + A1^2*A3*A4*L^3*MU*T^2 + A1^2*A3*A4*L^2*MU*Q*T^2 - A1^2*A3*A4*L^2*MU*T^2*WP + A1^2*A3*A4*L^2*MU*T*w + 3*A1^2*A3*A6*L^4*MU*T^2 + 2*A1^2*A3*A6*L^3*MU*Q*T^2 - 2*A1^2*A3*A6*L^3*MU*T^2*WP + 2*A1^2*A3*A6*L^3*MU*T*w - 3*A1^2*A3*L*MU*T^2 - A1^2*A3*MU*Q*T^2 + A1^2*A3*MU*T^2*WP - A1^2*A3*MU*T*w + A1^2*A4^2*L^4*T^2 + 3*A1^2*A4*A6*L^5*T^2 - 2*A1^2*A4*L^2*MU*T + 2*A1^2*A6^2*L^6*T^2 - 4*A1^2*A6*L^3*MU*T + A1^2*A6*L^3*T^2 + 2*A1^2*MU*T - A1^2*T^2 + A1*A2^2*L^2*T - A1*A2*A3^2*L^3*MU*T^2 - A1*A2*A3^2*L^2*MU*Q*T^2 + A1*A2*A3^2*L^2*MU*T^2*WP - A1*A2*A3^2*L^2*MU*T*w + A1*A2*A3*A4*L^4*T^2 + A1*A2*A3*A4*L^3*Q*T^2 - A1*A2*A3*A4*L^3*T^2*WP + A1*A2*A3*A4*L^3*T*w + 2*A1*A2*A3*A6*L^5*T^2 + 2*A1*A2*A3*A6*L^4*Q*T^2 - 2*A1*A2*A3*A6*L^4*T^2*WP + 2*A1*A2*A3*A6*L^4*T*w + 2*A1*A2*A3*L^2*MU*T - A1*A2*A3*L^2*T^2 - A1*A2*A3*L*Q*T^2 + A1*A2*A3*L*T^2*WP - A1*A2*A3*L*T*w - 2*A1*A2*A6*L^4*T + 4*A1*A2*L*T + A1*A3^2*A4*L^3*MU*Q*T^2 - A1*A3^2*A4*L^2*MU*Q*T^2*WP + A1*A3^2*A4*L^2*MU*Q*T*w + A1*A3^2*A6*L^5*MU*T^2 + 3*A1*A3^2*A6*L^4*MU*Q*T^2 - A1*A3^2*A6*L^4*MU*T^2*WP + A1*A3^2*A6*L^4*MU*T*w - 2*A1*A3^2*A6*L^3*MU*Q*T^2*WP + 2*A1*A3^2*A6*L^3*MU*Q*T*w - 2*A1*A3^2*L^2*MU*T^2 - 3*A1*A3^2*L*MU*Q*T^2 + 2*A1*A3^2*L*MU*T^2*WP - 2*A1*A3^2*L*MU*T*w + A1*A3^2*MU*Q*T^2*WP - A1*A3^2*MU*Q*T*w + A1*A3*A4^2*L^5*T^2 + A1*A3*A4^2*L^4*Q*T^2 - A1*A3*A4^2*L^4*T^2*WP + A1*A3*A4^2*L^4*T*w + 3*A1*A3*A4*A6*L^6*T^2 + 3*A1*A3*A4*A6*L^5*Q*T^2 - 3*A1*A3*A4*A6*L^5*T^2*WP + 3*A1*A3*A4*A6*L^5*T*w - A1*A3*A4*L^3*MU*T - A1*A3*A4*L^2*MU*Q*T + A1*A3*A4*L^2*MU*T*WP - A1*A3*A4*L^2*MU*w + 2*A1*A3*A6^2*L^7*T^2 + 2*A1*A3*A6^2*L^6*Q*T^2 - 2*A1*A3*A6^2*L^6*T^2*WP + 2*A1*A3*A6^2*L^6*T*w - 4*A1*A3*A6*L^4*MU*T + A1*A3*A6*L^4*T^2 - 2*A1*A3*A6*L^3*MU*Q*T + 2*A1*A3*A6*L^3*MU*T*WP - 2*A1*A3*A6*L^3*MU*w + A1*A3*A6*L^3*Q*T^2 - A1*A3*A6*L^3*T^2*WP + A1*A3*A6*L^3*T*w + 5*A1*A3*L*MU*T - A1*A3*L*T^2 + A1*A3*MU*Q*T - A1*A3*MU*T*WP + A1*A3*MU*w - A1*A3*Q*T^2 + A1*A3*T^2*WP - A1*A3*T*w - A1*A4^2*L^4*T - 4*A1*A4*A6*L^5*T + A1*A4*L^2*MU + 2*A1*A4*L^2*T - 3*A1*A6^2*L^6*T + 2*A1*A6*L^3*MU - A1*MU + 3*A1*T + A2^2*A3*L^3*T + A2^2*A3*L^2*w - 2*A2^2*L^2 - A2*A3^3*L^3*MU*Q*T^2 + A2*A3^3*L^2*MU*Q*T^2*WP - A2*A3^3*L^2*MU*Q*T*w + A2*A3^2*A4*L^4*Q*T^2 - A2*A3^2*A4*L^3*Q*T^2*WP + A2*A3^2*A4*L^3*Q*T*w + 2*A2*A3^2*A6*L^5*Q*T^2 - 2*A2*A3^2*A6*L^4*Q*T^2*WP + 2*A2*A3^2*A6*L^4*Q*T*w + A2*A3^2*L^3*MU*T + A2*A3^2*L^2*MU*Q*T - A2*A3^2*L^2*MU*T*WP + A2*A3^2*L^2*MU*w - A2*A3^2*L^2*Q*T^2 + A2*A3^2*L*Q*T^2*WP - A2*A3^2*L*Q*T*w + A2*A3*A4*L^4*T - A2*A3*A4*L^3*Q*T + A2*A3*A4*L^3*T*WP + A2*A3*A4*L^3*w - 2*A2*A3*A6*L^4*Q*T + 2*A2*A3*A6*L^4*T*WP - A2*A3*L^2*MU + 3*A2*A3*L^2*T + A2*A3*L*Q*T - A2*A3*L*T*WP + 3*A2*A3*L*w - 3*A2*A4*L^3 - 2*A2*A6*L^4 - 5*A2*L + A3^3*A6*L^5*MU*Q*T^2 - A3^3*A6*L^4*MU*Q*T^2*WP + A3^3*A6*L^4*MU*Q*T*w - 2*A3^3*L^2*MU*Q*T^2 + 2*A3^3*L*MU*Q*T^2*WP - 2*A3^3*L*MU*Q*T*w + A3^2*A4^2*L^5*Q*T^2 - A3^2*A4^2*L^4*Q*T^2*WP + A3^2*A4^2*L^4*Q*T*w + 3*A3^2*A4*A6*L^6*Q*T^2 - 3*A3^2*A4*A6*L^5*Q*T^2*WP + 3*A3^2*A4*A6*L^5*Q*T*w + 2*A3^2*A6^2*L^7*Q*T^2 - 2*A3^2*A6^2*L^6*Q*T^2*WP + 2*A3^2*A6^2*L^6*Q*T*w - A3^2*A6*L^5*MU*T - A3^2*A6*L^4*MU*Q*T + A3^2*A6*L^4*MU*T*WP - A3^2*A6*L^4*MU*w + A3^2*A6*L^4*Q*T^2 - A3^2*A6*L^3*Q*T^2*WP + A3^2*A6*L^3*Q*T*w + 2*A3^2*L^2*MU*T + 2*A3^2*L*MU*Q*T - 2*A3^2*L*MU*T*WP + 2*A3^2*L*MU*w - A3^2*L*Q*T^2 + A3^2*Q*T^2*WP - A3^2*Q*T*w - A3*A4^2*L^4*Q*T + A3*A4^2*L^4*T*WP - A3*A4*A6*L^6*T - 3*A3*A4*A6*L^5*Q*T + 3*A3*A4*A6*L^5*T*WP - A3*A4*A6*L^5*w + 2*A3*A4*L^3*T + 2*A3*A4*L^2*w - A3*A6^2*L^7*T - 2*A3*A6^2*L^6*Q*T + 2*A3*A6^2*L^6*T*WP - A3*A6^2*L^6*w + A3*A6*L^4*MU + A3*A6*L^4*T - A3*A6*L^3*Q*T + A3*A6*L^3*T*WP + A3*A6*L^3*w - 2*A3*L*MU + 2*A3*L*T + A3*Q*T - A3*T*WP + 2*A3*w - A4^2*L^4 - A4*A6*L^5 - 4*A4*L^2 - 3*A6*L^3 - 3) * hwsub

end S_WeierstrassCurve_formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed
end P2MW
export P2MW.S_WeierstrassCurve_formalW_mul_eq_sub_mul_subst_pderiv_formalGroupLawFixed (solution)
