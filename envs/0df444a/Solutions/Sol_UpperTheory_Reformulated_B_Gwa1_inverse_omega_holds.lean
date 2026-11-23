-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Gwa1.inverse_omega_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:27.080094+00:00
-- url     : https://prove2.me/submissions/0c3f7681-e8b9-4d24-8ade-811ab17087b8

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InverseOmegaHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace UpperTheory.Reformulated.B.Gwa1
open PowerSeries
private theorem C_mem {R : Type*} [CommRing R] {O : Subring R} (n : ℕ) {a : R} (ha : a ∈ O) :
    (C a : R⟦X⟧) ∈ lowIn O n := by
  intro k _
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact O.zero_mem
private theorem X_mem {R : Type*} [CommRing R] (O : Subring R) (n : ℕ) :
    (X : R⟦X⟧) ∈ lowIn O n := by
  intro k _
  rw [coeff_X]
  split_ifs
  · exact O.one_mem
  · exact O.zero_mem
private theorem X_mul_mem {R : Type*} [CommRing R] {O : Subring R} {n : ℕ} {f : R⟦X⟧}
    (hf : f ∈ lowIn O n) : X * f ∈ lowIn O (n + 1) := by
  intro k hk
  cases k with
  | zero => rw [coeff_zero_X_mul]; exact O.zero_mem
  | succ k => rw [coeff_succ_X_mul]; exact hf k (by omega)
private theorem w_mem {R : Type*} [CommRing R] {O : Subring R} {a₁ a₂ a₃ a₄ a₆ : R}
    (h₁ : a₁ ∈ O) (h₂ : a₂ ∈ O) (h₃ : a₃ ∈ O) (h₄ : a₄ ∈ O) (h₆ : a₆ ∈ O) {w : R⟦X⟧}
    (hw : w = 1 + C a₁ * X * w + C a₂ * X ^ 2 * w + C a₃ * X ^ 3 * w ^ 2 + C a₄ * X ^ 4 * w ^ 2
      + C a₆ * X ^ 6 * w ^ 3) (n : ℕ) : w ∈ lowIn O n := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    have e : w = 1 + X * (C a₁ * w + C a₂ * X * w + C a₃ * X ^ 2 * w ^ 2 + C a₄ * X ^ 3 * w ^ 2
      + C a₆ * X ^ 5 * w ^ 3) := by linear_combination hw
    have hX := X_mem O n
    rw [e]
    exact add_mem (one_mem _) (X_mul_mem (add_mem (add_mem (add_mem (add_mem
      (mul_mem (C_mem n h₁) ih)
      (mul_mem (mul_mem (C_mem n h₂) hX) ih))
      (mul_mem (mul_mem (C_mem n h₃) (pow_mem hX _)) (pow_mem ih _)))
      (mul_mem (mul_mem (C_mem n h₄) (pow_mem hX _)) (pow_mem ih _)))
      (mul_mem (mul_mem (C_mem n h₆) (pow_mem hX _)) (pow_mem ih _))))
private theorem dX_eq {R : Type*} [CommRing R] (f : R⟦X⟧) : dX f = derivative R f := by
  ext n
  rw [coeff_derivative, dX, coeff_mk, mul_comm]
private theorem key {R : Type*} [CommRing R] {a₁ a₂ a₃ a₄ a₆ : R} {w : R⟦X⟧}
    (hw : w = 1 + C a₁ * X * w + C a₂ * X ^ 2 * w + C a₃ * X ^ 3 * w ^ 2 + C a₄ * X ^ 4 * w ^ 2
      + C a₆ * X ^ 6 * w ^ 3) :
    (1 - C a₁ * X - C a₂ * X ^ 2 - 2 * (C a₃ * X ^ 3 * w) - 2 * (C a₄ * X ^ 4 * w)
      - 3 * (C a₆ * X ^ 6 * w ^ 2)) * (-2 * w - X * dX w)
      = w * (C a₁ * X + C a₃ * X ^ 3 * w - 2) := by
  have h := congrArg (derivative R) hw
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, derivative_C, derivative_X,
    Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul] at h
  rw [dX_eq]
  push_cast at h
  linear_combination (-X) * h
private theorem dX_flog {p : ℕ} [Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p])
    (w : ℂ_[p]⟦X⟧) : dX (flog W w) = omegaW W w := by
  ext n
  have hn : ((n : ℂ_[p]) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  rw [dX, coeff_mk, flog, coeff_mk, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel,
    Nat.cast_add_one, mul_div_cancel₀ _ hn]
end UpperTheory.Reformulated.B.Gwa1
end

set_option autoImplicit false

open PowerSeries
namespace UpperTheory.Reformulated.B.Gwa1
theorem _root_.solution :
    UpperTheory.Reformulated.B.Gwa1.InvOmega := by
  intro p _ W w h₁ h₂ h₃ h₄ h₆ hw
  have hw' : w = 1 + C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * X ^ 3 * w ^ 2
      + C W.a₄ * X ^ 4 * w ^ 2 + C W.a₆ * X ^ 6 * w ^ 3 := hw
  refine ⟨1 - C W.a₁ * X - C W.a₂ * X ^ 2 - 2 * (C W.a₃ * X ^ 3 * w) - 2 * (C W.a₄ * X ^ 4 * w)
      - 3 * (C W.a₆ * X ^ 6 * w ^ 2), fun n => ?_, ?_⟩
  · have hX := X_mem (ball p) (n + 1)
    have ih := w_mem (O := ball p) h₁ h₂ h₃ h₄ h₆ hw' (n + 1)
    have c₁ := C_mem (O := ball p) (n + 1) h₁
    have c₂ := C_mem (O := ball p) (n + 1) h₂
    have c₃ := C_mem (O := ball p) (n + 1) h₃
    have c₄ := C_mem (O := ball p) (n + 1) h₄
    have c₆ := C_mem (O := ball p) (n + 1) h₆
    exact (sub_mem (sub_mem (sub_mem (sub_mem (sub_mem (one_mem _) (mul_mem c₁ hX))
      (mul_mem c₂ (pow_mem hX _)))
      (mul_mem (ofNat_mem _ 2) (mul_mem (mul_mem c₃ (pow_mem hX _)) ih)))
      (mul_mem (ofNat_mem _ 2) (mul_mem (mul_mem c₄ (pow_mem hX _)) ih)))
      (mul_mem (ofNat_mem _ 3) (mul_mem (mul_mem c₆ (pow_mem hX _)) (pow_mem ih _))) :
        _ ∈ lowIn (ball p) (n + 1)) n (Nat.lt_succ_self n)
  · have h0 : constantCoeff w = 1 := by
      have h := congrArg constantCoeff hw'
      simpa using h
    have hu : constantCoeff (w * (C W.a₁ * X + C W.a₃ * X ^ 3 * w - 2)) ≠ 0 := by
      simp [h0, map_ofNat]
    have ho : omegaW W w = (-2 * w - X * dX w) * (w * (C W.a₁ * X + C W.a₃ * X ^ 3 * w - 2))⁻¹ :=
      rfl
    rw [dX_flog, ho, ← mul_assoc, key hw']
    exact PowerSeries.mul_inv_cancel _ hu
end UpperTheory.Reformulated.B.Gwa1
