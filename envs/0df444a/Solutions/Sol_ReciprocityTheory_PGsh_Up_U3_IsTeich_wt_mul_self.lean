-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.IsTeich.wt_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:18:51.918647+00:00
-- url     : https://prove2.me/submissions/df4a2bec-6585-460f-8919-1424a4e24eac

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_pow_pred

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
theorem _root_.solution {a : ZMod p} (ha : a ≠ 0) : wt ω a * ω a = 1 := by
  unfold wt
  rw [← pow_succ]
  have e : 2 * p - 3 + 1 = (p - 1) * 2 := by
    have := hp.out.two_le
    omega
  rw [e, pow_mul, hω.pow_pred ha, one_pow]
end ReciprocityTheory.PGsh.Up.U3.IsTeich
