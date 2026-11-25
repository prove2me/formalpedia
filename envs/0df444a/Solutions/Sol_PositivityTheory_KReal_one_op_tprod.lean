-- Prove2me | solution 1 for PositivityTheory.KReal.one_op_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:16:14.560821+00:00
-- url     : https://prove2.me/submissions/c0c0b7ca-30fe-4368-9c52-f86f07efab9b

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_TensorIrr
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpectrumNonemptyOfCountableRank
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_Tensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.KReal
variable {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
namespace PositivityTheory.KReal
theorem _root_.solution (i : ι) (f : Module.End ℂ (M i)) (x : ∀ j, M j) :
    one_op i f (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (Function.update x i (f (x i))) := by
  rw [one_op, PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]
end PositivityTheory.KReal
