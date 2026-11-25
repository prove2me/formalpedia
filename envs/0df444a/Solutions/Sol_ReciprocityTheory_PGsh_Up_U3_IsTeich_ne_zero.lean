-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.IsTeich.ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:52:37.928505+00:00
-- url     : https://prove2.me/submissions/12bd1ed4-47eb-4fa5-b0d0-a728ed54ef1d

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_v_eq_one

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
theorem _root_.solution {a : ZMod p} (ha : a ≠ 0) : ω a ≠ 0 := by
  intro h
  have h1 := hω.v_eq_one ha
  rw [h, map_zero] at h1
  exact zero_ne_one h1
end ReciprocityTheory.PGsh.Up.U3.IsTeich
