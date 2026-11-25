-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.IsTeich.lam_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:35:34.924568+00:00
-- url     : https://prove2.me/submissions/9691e37f-8d28-4e98-9997-b63820f77cf2

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_wt_mul
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_wt_inv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
namespace IsTeich
variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω
end IsTeich
section wt
namespace IsTeich
variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω
private theorem lam_eq_sum_wt_mul_sub (f : ZMod p → C) : lam ω f = ∑ a, wt ω a * (f a - f 0) := by
  simp [lam, u0, sS, sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
end IsTeich
end wt
section hopf
variable (hv : v.Integers R)
include hv
variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω
end hopf
end ReciprocityTheory.PGsh.Up.U3
end
end

set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
open ReciprocityTheory.PGsh.Up.U3.IsTeich
variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω
namespace ReciprocityTheory.PGsh.Up.U3.IsTeich
theorem _root_.solution (φ : ZMod p → C) (h : ZMod p) :
    ∑ a, u0 ω a * φ (h * a) = ω h * ∑ a, u0 ω a * φ a := by
  have e : ∀ g : ZMod p → C, ∑ a, u0 ω a * g a = ∑ a, wt ω a * (g a - g 0) :=
    fun g => lam_eq_sum_wt_mul_sub hω g
  rw [e (fun a => φ (h * a)), e φ]
  simp only [mul_zero]
  by_cases hh : h = 0
  · subst hh
    simp [hω.zero]
  · rw [Finset.mul_sum]
    calc ∑ a, wt ω a * (φ (h * a) - φ 0)
        = ∑ a, (fun b => wt ω (h⁻¹ * b) * (φ b - φ 0)) (Equiv.mulLeft₀ h hh a) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          simp [inv_mul_cancel_left₀ hh]
      _ = ∑ b, wt ω (h⁻¹ * b) * (φ b - φ 0) := Equiv.sum_comp (Equiv.mulLeft₀ h hh) (fun b => wt ω (h⁻¹ * b) * (φ b - φ 0))
      _ = ∑ b, ω h * (wt ω b * (φ b - φ 0)) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hω.wt_mul, hω.wt_inv hh]
          ring
end ReciprocityTheory.PGsh.Up.U3.IsTeich
