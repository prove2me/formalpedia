-- Prove2me | solution 1 for RandomDimReduction.Channel.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T17:32:05.659208+00:00
-- url     : https://prove2.me/submissions/d50d283d-9a9b-47d3-b745-48dcf9a2781a

import Definitions.Def_RandomDimReduction_Channel_Moment
import Definitions.Def_RandomDimReduction_Channel_Schur
import Mathlib.LinearAlgebra.Matrix.Bilinear

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq Matrix.normedAddCommGroup

local instance {ι : Type} [Fintype ι] : ContinuousENorm (Matrix ι ι ℂ) :=
  @SeminormedAddGroup.toContinuousENorm _ inferInstance

lemma tensor_perm_commute (n d : ℕ) (A : Op (Fin d)) (π : Equiv.Perm (Fin n)) :
    tensor n A * QAlgorithms.Schur.tensorPermutation d n π =
      QAlgorithms.Schur.tensorPermutation d n π * tensor n A := by
  have he (i j : Word n d) : i = j ∘ π.symm ↔ j = i ∘ π := by
    constructor <;> intro h <;> subst_vars <;> funext t <;> simp
  ext i j
  simp only [Matrix.mul_apply, QAlgorithms.Schur.tensorPermutation, Matrix.of_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [he]
  simp only [ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [tensor, Function.comp_apply]
  simpa using (Equiv.prod_comp π (fun t => A (i t) (j (π.symm t)))).symm

lemma continuous_tensor (n d : ℕ) : Continuous (tensor (a := Fin d) (b := Fin d) n) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_finsetProd _ fun t _ => (continuous_apply (j t)).comp (continuous_apply (i t))

end RandomDimReduction.Channel

open RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d)
    (π : Equiv.Perm (Fin n)) :
    moment n k d * QAlgorithms.Schur.tensorPermutation d n π =
      QAlgorithms.Schur.tensorPermutation d n π * moment n k d := by
  let f := fun V : Matrix.unitaryGroup (Fin d) ℂ =>
    tensor n (randomEmbedding k V * (randomEmbedding k V)ᴴ)
  have hc : Continuous f := by
    apply (continuous_tensor n d).comp
    exact (continuous_subtype_val.matrix_mul continuous_const).matrix_mul
      (continuous_subtype_val.matrix_mul continuous_const).matrix_conjTranspose
  have hf := hc.integrable_of_hasCompactSupport (μ := MixedCloning.Optimal.haar d) (HasCompactSupport.of_compactSpace f)
  let P := QAlgorithms.Schur.tensorPermutation d n π
  change (∫ V, f V ∂MixedCloning.Optimal.haar d) * P =
    P * (∫ V, f V ∂MixedCloning.Optimal.haar d)
  calc
    _ = ∫ V, f V * P ∂MixedCloning.Optimal.haar d :=
      ((mulRightLinearMap (Word n d) ℝ P).toContinuousLinearMap.integral_comp_comm hf).symm
    _ = ∫ V, P * f V ∂MixedCloning.Optimal.haar d :=
      integral_congr_ae (Filter.Eventually.of_forall fun V => tensor_perm_commute n d _ π)
    _ = _ := (mulLeftLinearMap (Word n d) ℝ P).toContinuousLinearMap.integral_comp_comm hf

