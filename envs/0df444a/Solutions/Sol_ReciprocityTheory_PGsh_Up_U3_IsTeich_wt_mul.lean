-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.IsTeich.wt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:40:06.861898+00:00
-- url     : https://prove2.me/submissions/2327b32d-0e36-4d31-a03b-bc36a0aa40d0

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
theorem _root_.solution (a b : ZMod p) : wt ω (a * b) = wt ω a * wt ω b := by
  unfold wt
  rw [hω.mul, mul_pow]
end ReciprocityTheory.PGsh.Up.U3.IsTeich
