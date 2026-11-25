-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.IsTeich.lam_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:49:46.291628+00:00
-- url     : https://prove2.me/submissions/97d15683-c5be-4252-8435-2f8ce75414ca

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight
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
theorem _root_.solution (f : ZMod p → C) : lam ω f = ∑ a, wt ω a * (f a - f 0) := by
  exact lam_eq_sum_wt_mul_sub hω f
end ReciprocityTheory.PGsh.Up.U3.IsTeich
