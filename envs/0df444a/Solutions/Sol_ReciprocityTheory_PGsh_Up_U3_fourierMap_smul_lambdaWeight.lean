-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.fourierMap_smul_lambdaWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:49:47.912799+00:00
-- url     : https://prove2.me/submissions/98fc61c8-2611-4d93-8251-a6a9b63a7789

import Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight
import Definitions.Def_ReciprocityTheory_DualLattices_FourierMapSmulLambdaWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution {ω : ZMod p → C} (hω : IsTeich v ω) {ζ : C}
    (e : ZMod p ≃ AddChar (ZMod p) C) (he2 : ∀ h a, e h a = ζ ^ (h * a).val) (c : C) :
    fourier (R := R) (fun h a => e h a) (fun a => c * u0 ω a) =
      fun h => (c * ∑ a, u0 ω a * ζ ^ a.val) * ω h := by
  have hω0 : ∀ h : ZMod p, h ≠ 0 → ω h ≠ 0 := by
    intro h hh
    have := hω.sep h 0 hh
    rw [hω.zero, sub_zero] at this
    intro h0
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpow1 : ∀ h : ZMod p, h ≠ 0 → ω h ^ (p - 1) = 1 := by
    intro h hh
    have e1 := hω.pow h
    have : ω h ^ (p - 1) * ω h = 1 * ω h := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, e1]
    exact mul_right_cancel₀ (hω0 h hh) this
  have hwt : ∀ h : ZMod p, h ≠ 0 → wt ω h * ω h = 1 := by
    intro h hh
    simp only [wt]
    rw [← pow_succ, show 2 * p - 3 + 1 = (p - 1) + (p - 1) by omega, pow_add, hpow1 h hh, one_mul]
  have hwtmul : ∀ a b : ZMod p, wt ω (a * b) = wt ω a * wt ω b := by
    intro a b; simp only [wt, hω.mul, mul_pow]
  have hwtinv : ∀ h : ZMod p, h ≠ 0 → wt ω h⁻¹ = ω h := by
    intro h hh
    have hi : h⁻¹ ≠ 0 := inv_ne_zero hh
    have e1 := hwt h⁻¹ hi
    have e2 : ω h⁻¹ * ω h = 1 := by rw [← hω.mul, inv_mul_cancel₀ hh, hω.one]
    calc wt ω h⁻¹ = wt ω h⁻¹ * (ω h⁻¹ * ω h) := by rw [e2, mul_one]
      _ = ω h := by rw [← mul_assoc, e1, one_mul]
  have hwt0 : wt ω 0 = 0 := by
    simp only [wt, hω.zero]; exact zero_pow (by omega)
  have hS : ∀ h : ZMod p, h ≠ 0 → sS ω = ω h * sS ω := by
    intro h hh
    have := Fintype.sum_bijective (h⁻¹ * ·) (mulLeft_bijective₀ h⁻¹ (inv_ne_zero hh))
      (fun b => wt ω (h⁻¹ * b)) (wt ω) (fun _ => rfl)
    simp only [hwtmul, hwtinv h hh, ← Finset.mul_sum] at this
    simp only [sS]; exact this.symm
  have hu : ∀ h : ZMod p, h ≠ 0 → ∀ b, u0 ω (h⁻¹ * b) = ω h * u0 ω b := by
    intro h hh b
    simp only [u0]
    by_cases hb : b = 0
    · subst hb
      simp only [mul_zero, if_true, hwt0]
      nth_rewrite 1 [hS h hh]; ring
    · have : h⁻¹ * b ≠ 0 := mul_ne_zero (inv_ne_zero hh) hb
      simp only [this, hb, if_false, sub_zero, hwtmul, hwtinv h hh]
  funext h
  simp only [L2.fourier, LinearMap.coe_mk, AddHom.coe_mk, he2]
  by_cases hh : h = 0
  · subst hh
    simp only [zero_mul, ZMod.val_zero, pow_zero, mul_one, hω.zero, mul_zero]
    rw [← Finset.mul_sum]
    simp only [u0, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [sS]
  · have hb := Fintype.sum_bijective (h⁻¹ * ·) (mulLeft_bijective₀ h⁻¹ (inv_ne_zero hh))
      (fun b => c * u0 ω (h⁻¹ * b) * ζ ^ (h * (h⁻¹ * b)).val)
      (fun a => c * u0 ω a * ζ ^ (h * a).val) (fun _ => rfl)
    rw [← hb]
    simp only [hu h hh, ← mul_assoc, mul_inv_cancel₀ hh, one_mul]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
end ReciprocityTheory.PGsh.Up.U3
