-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.lam_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:48:04.680691+00:00
-- url     : https://prove2.me/submissions/2f1d1449-d090-40a9-bde0-270128c39f2e

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
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution (ω : ZMod p → C) {ι : Type} [Fintype ι] (c : ι → C) (g : ι → ZMod p → C) :
    lam ω (fun a => ∑ j, c j * g j a) = ∑ j, c j * lam ω (g j) := by
  unfold lam
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
  ring
end ReciprocityTheory.PGsh.Up.U3
