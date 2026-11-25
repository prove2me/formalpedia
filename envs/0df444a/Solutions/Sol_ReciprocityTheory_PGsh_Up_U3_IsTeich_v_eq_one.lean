-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.IsTeich.v_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:42:50.236033+00:00
-- url     : https://prove2.me/submissions/b3750608-9a6d-401a-b47b-6c6bda43e00f

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
theorem _root_.solution {a : ZMod p} (ha : a ≠ 0) : v (ω a) = 1 := by
  have h := hω.sep a 0 ha
  rwa [hω.zero, sub_zero] at h
end ReciprocityTheory.PGsh.Up.U3.IsTeich
