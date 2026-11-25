-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.IsTeich.wt_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:29:44.651996+00:00
-- url     : https://prove2.me/submissions/6746d066-7729-4b3a-af56-d7b5299e6b9b

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_wt_mul_self

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
theorem _root_.solution {a : ZMod p} (ha : a ≠ 0) : wt ω a⁻¹ = ω a := by
  have h1 := hω.wt_mul_self (inv_ne_zero ha)
  have h2 : ω a⁻¹ * ω a = 1 := by
    rw [← hω.mul, inv_mul_cancel₀ ha, hω.one]
  calc wt ω a⁻¹ = wt ω a⁻¹ * (ω a⁻¹ * ω a) := by rw [h2, mul_one]
    _ = ω a := by rw [← mul_assoc, h1, one_mul]
end ReciprocityTheory.PGsh.Up.U3.IsTeich
