-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.IsTeich.int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:40:28.072894+00:00
-- url     : https://prove2.me/submissions/27f53f55-06d9-4d54-888b-c839307c28fd

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
theorem _root_.solution (a : ZMod p) : v (ω a) ≤ 1 := by
  by_cases ha : a = 0
  · rw [ha, hω.zero, map_zero]
    exact zero_le
  · have h := hω.sep a 0 ha
    rw [hω.zero, sub_zero] at h
    exact h.le
end ReciprocityTheory.PGsh.Up.U3.IsTeich
