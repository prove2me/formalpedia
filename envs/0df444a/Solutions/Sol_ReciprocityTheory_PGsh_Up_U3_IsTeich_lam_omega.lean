-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.IsTeich.lam_omega
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:27:21.344774+00:00
-- url     : https://prove2.me/submissions/d1d70725-459a-4a61-8ac1-a27a5123813e

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_wt_zero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_wt_mul_self
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
theorem _root_.solution : lam ω ω = (p : C) - 1 := by
  rw [lam_eq_sum_wt_mul_sub hω, hω.zero]
  simp only [sub_zero]
  have h1 : ∀ a, wt ω a * ω a = 1 - if a = 0 then 1 else 0 := fun a => by
    split_ifs with ha
    · rw [ha, hω.wt_zero, zero_mul, sub_self]
    · rw [hω.wt_mul_self ha, sub_zero]
  simp only [h1, Finset.sum_sub_distrib]
  simp
end ReciprocityTheory.PGsh.Up.U3.IsTeich
