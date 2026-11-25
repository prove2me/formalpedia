-- Prove2me | solution 1 for PositivityTheory.KReal.map_mem_of_one_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:58.975296+00:00
-- url     : https://prove2.me/submissions/d4f452fa-ef4e-496d-91e3-5d990cd00108

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
theorem _root_.solution [Fintype ι] (N : Submodule ℂ (PiTensorProduct ℂ M))
    (hN : ∀ i (f : Module.End ℂ (M i)), ∀ x ∈ N, one_op i f x ∈ N)
    (f : ∀ i, Module.End ℂ (M i)) (x : PiTensorProduct ℂ M) (hx : x ∈ N) : PiTensorProduct.map f x ∈ N := by
  have key : ∀ s : Finset ι,
      PiTensorProduct.map (fun j => if j ∈ s then f j else (LinearMap.id : M j →ₗ[ℂ] M j)) x ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hx
    | insert i s hi ih =>
      have e : PiTensorProduct.map (fun j => if j ∈ insert i s then f j else (LinearMap.id : M j →ₗ[ℂ] M j)) =
          one_op i (f i) ∘ₗ
            PiTensorProduct.map (fun j => if j ∈ s then f j else (LinearMap.id : M j →ₗ[ℂ] M j)) := by
        rw [one_op, ← PiTensorProduct.map_comp]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj, Function.update_of_ne hj]
      rw [e]
      exact hN i (f i) _ ih
  simpa using key Finset.univ
end PositivityTheory.KReal
