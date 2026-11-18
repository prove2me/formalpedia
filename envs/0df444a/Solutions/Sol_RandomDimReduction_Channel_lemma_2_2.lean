-- Prove2me | solution 1 for RandomDimReduction.Channel.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T17:42:11.78438+00:00
-- url     : https://prove2.me/submissions/64ec094f-4dcd-4100-9327-40567efddc85

import Definitions.Def_RandomDimReduction_Channel_Moment
import Mathlib.LinearAlgebra.Matrix.Bilinear

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma tensor_mul {a b c : Type} [Fintype b] (n : ℕ)
    (A : Matrix a b ℂ) (B : Matrix b c ℂ) :
    tensor n (A * B) = tensor n A * tensor n B := by
  ext i j
  simp only [tensor, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum fun t z => A (i t) z * B z (j t)

lemma tensor_conjTranspose {a b : Type} (n : ℕ) (A : Matrix a b ℂ) :
    tensor n Aᴴ = (tensor n A)ᴴ := by
  ext i j
  simp [tensor, Matrix.conjTranspose_apply]

lemma tensor_one {a : Type} [DecidableEq a] (n : ℕ) :
    tensor n (1 : Op a) = 1 := by
  ext i j
  simp only [tensor, Matrix.one_apply, Finset.prod_boole]
  simp [funext_iff]

lemma tensor_isometry {a b : Type} [Fintype a] [Fintype b] (n : ℕ)
    (A : Matrix a b ℂ) (h : Aᴴ * A = 1) :
    (tensor n A)ᴴ * tensor n A = 1 := by
  rw [← tensor_conjTranspose, ← tensor_mul, h, tensor_one]

end RandomDimReduction.Channel

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma isometry_columns_orthonormal {k d : ℕ} (W : Matrix (Fin d) (Fin k) ℂ)
    (hW : Wᴴ * W = 1) :
    Orthonormal ℂ (fun j => WithLp.toLp 2 (Wᵀ j)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_matrix_col_col, hW]
  exact Matrix.one_apply

lemma isometry_completion {k d : ℕ} (hkd : k ≤ d)
    (W : Matrix (Fin d) (Fin k) ℂ) (hW : Wᴴ * W = 1) :
    ∃ V : Matrix.unitaryGroup (Fin d) ℂ, randomEmbedding k V = W := by
  let v : Fin d → EuclideanSpace ℂ (Fin d) := fun i =>
    if h : i.val < k then WithLp.toLp 2 (Wᵀ ⟨i.val, h⟩) else 0
  let s : Set (Fin d) := {i | i.val < k}
  have hv : Orthonormal ℂ (s.domRestrict v) := by
    have h := (isometry_columns_orthonormal W hW).comp
      (fun i : s => (⟨i.val.val, i.property⟩ : Fin k)) (by
        intro i j he
        apply Subtype.ext
        exact Fin.ext (congrArg (fun z : Fin k => z.val) he))
    convert h using 1
    funext i
    simp only [Set.domRestrict, v, dif_pos (show i.val.val < k from i.property)]
    rfl
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let V : Matrix.unitaryGroup (Fin d) ℂ :=
    ⟨(EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b.toBasis,
      (EuclideanSpace.basisFun (Fin d) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  refine ⟨V, ?_⟩
  ext i j
  simp only [randomEmbedding, Matrix.mul_apply, baseEmbedding]
  have he (x : Fin d) : x.val = j.val ↔ x = Fin.castLE hkd j := by
    simp [Fin.ext_iff]
  simp only [he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change ((EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b.toBasis) i (Fin.castLE hkd j) = _
  rw [Module.Basis.toMatrix_apply]
  change (b (Fin.castLE hkd j)) i = W i j
  rw [hb _ j.isLt]
  simp [v, s]

end RandomDimReduction.Channel

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma quadratic_gram {a b : Type} [Fintype a] [Fintype b]
    (T : Matrix a b ℂ) (z : a → ℂ) :
    star z ⬝ᵥ ((T * Tᴴ) *ᵥ z) =
      ((‖WithLp.toLp 2 (Tᴴ *ᵥ z)‖ : ℝ)^2 : ℂ) := by
  calc
    _ = inner ℂ (WithLp.toLp 2 (Tᴴ *ᵥ z)) (WithLp.toLp 2 (Tᴴ *ᵥ z)) := by
      rw [← Matrix.mulVec_mulVec, dotProduct_mulVec]
      have hs : star z ᵥ* T = star (Tᴴ *ᵥ z) := by
        rw [star_mulVec, Matrix.conjTranspose_conjTranspose]
      rw [hs]
      simp only [PiLp.inner_apply, RCLike.inner_apply', dotProduct, Pi.star_apply, WithLp.ofLp_toLp, RCLike.star_def]
    _ = _ := by exact inner_self_eq_norm_sq_to_K _

lemma integral_gram_kernel {a b G : Type} [Fintype a] [Fintype b]
    [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (T : G → Matrix a b ℂ) (hT : Continuous T) (z : a → ℂ)
    (hz : (∫ g, T g * (T g)ᴴ ∂μ) *ᵥ z = 0) (g : G) :
    (T g)ᴴ *ᵥ z = 0 := by
  let q : Op a →ₗ[ℝ] ℝ :=
    { toFun A := (star z ⬝ᵥ (A *ᵥ z)).re
      map_add' A B := by simp [Matrix.add_mulVec, dotProduct_add]
      map_smul' r A := by simp [Matrix.smul_mulVec, dotProduct_smul] }
  let f : G → ℝ := fun g => ‖WithLp.toLp 2 ((T g)ᴴ *ᵥ z)‖ ^ 2
  have hc : Continuous f := by
    dsimp [f]
    fun_prop
  have hf := hc.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace f)
  have hi := (hT.matrix_mul hT.matrix_conjTranspose).integrable_of_hasCompactSupport
      (μ := μ) (HasCompactSupport.of_compactSpace _)
  have he : ∫ g, f g ∂μ = 0 := by
    have hq := q.toContinuousLinearMap.integral_comp_comm hi
    have heq : (fun g => q (T g * (T g)ᴴ)) = f := by
      funext g
      change (star z ⬝ᵥ ((T g * (T g)ᴴ) *ᵥ z)).re = _
      rw [quadratic_gram]
      simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, f]

    change (∫ g, q (T g * (T g)ᴴ) ∂μ) = q (∫ g, T g * (T g)ᴴ ∂μ) at hq
    rw [heq] at hq
    rw [hq]
    change (star z ⬝ᵥ ((∫ g, T g * (T g)ᴴ ∂μ) *ᵥ z)).re = 0
    simp [hz]
  have hzero : f = fun _ => 0 :=
    Measure.eq_of_ae_eq ((integral_eq_zero_iff_of_nonneg (fun g => sq_nonneg _) hf).mp he)
      hc continuous_const
  have hn : ‖WithLp.toLp 2 ((T g)ᴴ *ᵥ z)‖ = 0 := by
    have h := congrFun hzero g
    exact (sq_eq_zero_iff).mp h
  exact WithLp.toLp_injective 2 (by simpa using norm_eq_zero.mp hn)

end RandomDimReduction.Channel

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma toEuclideanLin_subspaceProjector {ι : Type} [Fintype ι]
    (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    Matrix.toEuclideanLin (subspaceProjector S) = S.starProjection.toLinearMap := by
  apply (EuclideanSpace.basisFun ι ℂ).toBasis.ext
  intro i
  ext j
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, subspaceProjector,
    EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct]

lemma subspaceProjector_isHermitian {ι : Type} [Fintype ι]
    (S : Submodule ℂ (EuclideanSpace ℂ ι)) : (subspaceProjector S).IsHermitian := by
  rw [← Matrix.isSymmetric_toEuclideanLin_iff, toEuclideanLin_subspaceProjector]
  exact S.starProjection_isSymmetric

end RandomDimReduction.Channel

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma continuous_tensor_rect {a b : Type} (n : ℕ) : Continuous (tensor (a := a) (b := b) n) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_finsetProd _ fun t _ => (continuous_apply (j t)).comp (continuous_apply (i t))

lemma moment_as_gram (n k d : ℕ) :
    moment n k d = ∫ V : Matrix.unitaryGroup (Fin d) ℂ,
      tensor n (randomEmbedding k V) * (tensor n (randomEmbedding k V))ᴴ
      ∂MixedCloning.Optimal.haar d := by
  unfold moment
  simp_rw [tensor_mul, tensor_conjTranspose]

lemma moment_kernel_annihilates_random (n k d : ℕ)
    (z : EuclideanSpace ℂ (Word n d))
    (hz : z ∈ LinearMap.ker (Matrix.toEuclideanLin (moment n k d)))
    (V : Matrix.unitaryGroup (Fin d) ℂ) :
    (tensor n (randomEmbedding k V))ᴴ *ᵥ z.ofLp = 0 := by
  have hz' : moment n k d *ᵥ z.ofLp = 0 := by
    exact congrArg WithLp.ofLp hz
  rw [moment_as_gram] at hz'
  haveI : (MixedCloning.Optimal.haar d).IsOpenPosMeasure := by
    dsimp [MixedCloning.Optimal.haar]
    infer_instance
  exact integral_gram_kernel (MixedCloning.Optimal.haar d)
    (fun V => tensor n (randomEmbedding k V))
    ((continuous_tensor_rect n).comp (continuous_subtype_val.matrix_mul continuous_const))
    z.ofLp hz' V

lemma kernel_times_tensor (n k d : ℕ) (hkd : k ≤ d)
    (W : Matrix (Fin d) (Fin k) ℂ) (hW : Wᴴ * W = 1) :
    kernelProjector n k d * tensor n W = 0 := by
  obtain ⟨V, hV⟩ := isometry_completion hkd W hW
  let S := LinearMap.ker (Matrix.toEuclideanLin (moment n k d))
  have hP := subspaceProjector_isHermitian S
  have hzero : (tensor n W)ᴴ * kernelProjector n k d = 0 := by
    apply Matrix.ext
    intro i j
    have hz := moment_kernel_annihilates_random n k d
      (S.starProjection ((EuclideanSpace.basisFun (Word n d) ℂ) j))
      (S.starProjection_apply_mem _) V
    rw [hV] at hz
    exact congrFun hz i
  have h := congrArg Matrix.conjTranspose hzero
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero, show (kernelProjector n k d)ᴴ = kernelProjector n k d from hP] using h

end RandomDimReduction.Channel

open RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d)
    (W : Matrix (Fin d) (Fin k) ℂ) (hW : Wᴴ * W = 1) (X₀ : Op (Word n k)) :
    let X := tensor n W * X₀ * (tensor n W)ᴴ
    kernelProjector n k d * X = 0 ∧ X * kernelProjector n k d = 0 := by
  have h := kernel_times_tensor n k d hkd W hW
  have hP : (kernelProjector n k d)ᴴ = kernelProjector n k d :=
    subspaceProjector_isHermitian _
  have h' : (tensor n W)ᴴ * kernelProjector n k d = 0 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero, hP] using
      congrArg Matrix.conjTranspose h
  constructor
  · simp only [← Matrix.mul_assoc, h, Matrix.zero_mul]
  · rw [Matrix.mul_assoc, h', Matrix.mul_zero]
