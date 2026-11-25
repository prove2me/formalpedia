-- Prove2me | solution 1 for PositivityTheory.KReal.tensorIrr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:17:33.582801+00:00
-- url     : https://prove2.me/submissions/1e8e3109-d195-46c8-80f0-9f17df3e43e7

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_TensorIrr
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpectrumNonemptyOfCountableRank
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_Tensor
import Theorems.Thm_PositivityTheory_KReal_dense_countable
import Theorems.Thm_PositivityTheory_KReal_one_op_mul
import Theorems.Thm_PositivityTheory_KReal_one_op_add
import Theorems.Thm_PositivityTheory_KReal_one_op_alg
import Theorems.Thm_PositivityTheory_KReal_one_op_fin
import Theorems.Thm_PositivityTheory_KReal_map_mem_of_one_op

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
namespace PositivityTheory.KReal
theorem _root_.solution : TensorIrr := by
  intro ι _ _ A M _ _ act hr hnt hirr N hN
  have hall : ∀ i (f : Module.End ℂ (M i)), ∀ x ∈ N, one_op i f x ∈ N := by
    intro i f x hx
    let B : Subalgebra ℂ (Module.End ℂ (M i)) :=
      { carrier := {b | ∀ y ∈ N, one_op i b y ∈ N}
        mul_mem' := fun {a b} ha hb y hy => by
          rw [one_op_mul]; exact ha _ (hb y hy)
        add_mem' := fun {a b} ha hb y hy => by
          rw [one_op_add]; exact N.add_mem (ha y hy) (hb y hy)
        algebraMap_mem' := fun c y hy => by
          rw [one_op_alg]; exact N.smul_mem c hy }
    obtain ⟨s, hs⟩ := one_op_fin i x
    have := hnt i
    obtain ⟨b, hb, hfb⟩ := dense_countable (hr i) B
      (fun P hP => hirr i P fun a y hy => hP (act i a) (hN i a) y hy) f s
    rw [hs f b hfb]
    exact hb x hx
  rw [or_iff_not_imp_left]
  intro h0
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  let b := fun i => Module.Basis.ofVectorSpace ℂ (M i)
  obtain ⟨p, hp⟩ : ∃ p, (Basis.piTensorProduct b).repr x p ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx0 ((Basis.piTensorProduct b).repr.map_eq_zero_iff.1 (Finsupp.ext hc))
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have e : PiTensorProduct.map (fun i => ((b i).coord (p i)).smulRight (v i)) =
      ((Basis.piTensorProduct b).coord p).smulRight (PiTensorProduct.tprod ℂ v) := by
    ext y
    simp [Basis.piTensorProduct_repr_tprod_apply, MultilinearMap.map_smul_univ]
  have h1 := map_mem_of_one_op N hall (fun i => ((b i).coord (p i)).smulRight (v i)) x hx
  rw [e, LinearMap.smulRight_apply] at h1
  exact (N.smul_mem_iff hp).1 h1
end PositivityTheory.KReal
