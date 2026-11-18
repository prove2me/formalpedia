-- Prove2me | solution 1 for RandomDimReduction.Channel.RTP_isQuantumChannel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T17:59:37.16336+00:00
-- url     : https://prove2.me/submissions/cd194a6c-b8b5-45e2-9090-69c4f19089c0

import Definitions.Def_RandomDimReduction_Channel_Moment
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_choi_completelyPositive

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open QAlgorithms.Papers.Independent.Dependency50.P26

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

lemma convex_posSemidef (ι : Type) [Fintype ι] :
    Convex ℝ {A : Op ι | A.PosSemidef} := by
  intro A hA B hB r s hr hs _
  exact (hA.smul hr).add (hB.smul hs)

lemma isClosed_posSemidef (ι : Type) [Fintype ι] :
    IsClosed {A : Op ι | A.PosSemidef} := by
  have hh : IsClosed {A : Op ι | A.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hq : IsClosed (⋂ v : ι → ℂ, {A : Op ι | 0 ≤ star v ⬝ᵥ (A *ᵥ v)}) := by
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    fun_prop
  convert hh.inter hq using 1
  ext A
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  exact Matrix.posSemidef_iff_dotProduct_mulVec

lemma integral_posSemidef {ι G : Type} [Fintype ι]
    [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] (f : G → Op ι)
    (hf : Continuous f) (hp : ∀ g, (f g).PosSemidef) :
    (∫ g, f g ∂μ).PosSemidef := by
  exact (convex_posSemidef ι).integral_mem (isClosed_posSemidef ι)
    (Filter.Eventually.of_forall hp)
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))

end RandomDimReduction.Channel

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma continuous_tensor_all {a b : Type} (n : ℕ) : Continuous (tensor (a := a) (b := b) n) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_finsetProd _ fun t _ => (continuous_apply (j t)).comp (continuous_apply (i t))

lemma moment_posSemidef (n k d : ℕ) : (moment n k d).PosSemidef := by
  unfold moment
  simp_rw [tensor_mul, tensor_conjTranspose]
  apply integral_posSemidef
  · exact ((continuous_tensor_all n).comp (continuous_subtype_val.matrix_mul continuous_const)).matrix_mul
      ((continuous_tensor_all n).comp (continuous_subtype_val.matrix_mul continuous_const)).matrix_conjTranspose
  · intro V
    exact Matrix.posSemidef_self_mul_conjTranspose _

lemma inverseRootMoment_isHermitian (n k d : ℕ) : (inverseRootMoment n k d).IsHermitian := by
  exact cfc_predicate _ _

end RandomDimReduction.Channel

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma toEuclideanLin_subspaceProjector {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    Matrix.toEuclideanLin (subspaceProjector S) = S.starProjection.toLinearMap := by
  apply (EuclideanSpace.basisFun ι ℂ).toBasis.ext
  intro i
  ext j
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, subspaceProjector,
    EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct]

lemma subspaceProjector_isHermitian {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Submodule ℂ (EuclideanSpace ℂ ι)) : (subspaceProjector S).IsHermitian := by
  rw [← Matrix.isSymmetric_toEuclideanLin_iff, toEuclideanLin_subspaceProjector]
  exact S.starProjection_isSymmetric

lemma subspaceProjector_idempotent {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    subspaceProjector S * subspaceProjector S = subspaceProjector S := by
  apply Matrix.toEuclideanLin.injective
  change Matrix.toLpLin 2 2 (_ * _) = _
  rw [Matrix.toLpLin_mul 2 2 2]
  change Matrix.toEuclideanLin (subspaceProjector S) ∘ₗ
    Matrix.toEuclideanLin (subspaceProjector S) = _
  rw [toEuclideanLin_subspaceProjector]
  exact congrArg ContinuousLinearMap.toLinearMap S.isIdempotentElem_starProjection

lemma subspaceProjector_posSemidef {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Submodule ℂ (EuclideanSpace ℂ ι)) : (subspaceProjector S).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (subspaceProjector S)
  rwa [subspaceProjector_isHermitian S, subspaceProjector_idempotent] at h

end RandomDimReduction.Channel

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma cfc_kernelProjector {ι : Type} [Fintype ι] [DecidableEq ι] (M : Op ι) (hM : M.IsHermitian) :
    cfc (fun x : ℝ => if x = 0 then 1 else 0) M =
      subspaceProjector (LinearMap.ker (Matrix.toEuclideanLin M)) := by
  let q : ℝ → ℝ := fun x => if x = 0 then 1 else 0
  let Q := cfc q M
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ M) :=
    M.finite_real_spectrum.continuousOn f
  have hQ : Q.IsHermitian := cfc_predicate _ _
  have hQ2 : Q * Q = Q := by
    change cfc q M * cfc q M = cfc q M
    rw [← cfc_mul q q M (hc q) (hc q)]
    apply cfc_congr
    intro x _
    dsimp [q]
    split_ifs <;> norm_num
  have hsa : IsSelfAdjoint M := hM
  have hMQ : M * Q = 0 := by
    change M * cfc q M = 0
    calc
      _ = cfc (fun x : ℝ => x) M * cfc q M := by rw [cfc_id' ℝ M hsa]
      _ = cfc (fun x : ℝ => x * q x) M := (cfc_mul _ _ _ (hc _) (hc _)).symm
      _ = 0 := by
        rw [← cfc_zero ℝ M]
        apply cfc_congr
        intro x _
        dsimp [q]
        split_ifs with hx
        · simp [hx]
        · simp
  have hPM : cfc (fun x : ℝ => x⁻¹) M * M = 1 - Q := by
    change cfc (fun x : ℝ => x⁻¹) M * M = 1 - cfc q M
    calc
      _ = cfc (fun x : ℝ => x⁻¹) M * cfc (fun x : ℝ => x) M := by rw [cfc_id' ℝ M hsa]
      _ = cfc (fun x : ℝ => x⁻¹ * x) M := (cfc_mul _ _ _ (hc _) (hc _)).symm
      _ = cfc (fun x : ℝ => 1 - q x) M := by
        apply cfc_congr
        intro x _
        dsimp [q]
        split_ifs with hx
        · simp [hx]
        · simp [hx]
      _ = 1 - cfc q M := by
        rw [cfc_sub (fun _ : ℝ => 1) q M (hc _) (hc _), cfc_const_one ℝ M hsa]
  let L := Matrix.toEuclideanLin Q
  have hi : IsIdempotentElem L := by
    change Matrix.toEuclideanLin Q ∘ₗ Matrix.toEuclideanLin Q = Matrix.toEuclideanLin Q
    have h := congrArg Matrix.toEuclideanLin hQ2
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using h
  have hs : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ
  have hr : LinearMap.range L = LinearMap.ker (Matrix.toEuclideanLin M) := by
    apply le_antisymm
    · rintro z ⟨v, rfl⟩
      have he : Matrix.toEuclideanLin M ∘ₗ Matrix.toEuclideanLin Q = 0 := by
        simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, map_zero] using
          congrArg Matrix.toEuclideanLin hMQ
      exact LinearMap.congr_fun he v
    · intro z hz
      refine ⟨z, ?_⟩
      have h := congrArg (fun A : Op ι => Matrix.toEuclideanLin A z) hPM
      have hz' : Matrix.toEuclideanLin M z = 0 := hz
      simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
        LinearMap.comp_apply, hz', map_zero, map_sub, Matrix.toLpLin_one,
        LinearMap.sub_apply, LinearMap.id_apply] at h
      exact (sub_eq_zero.mp h.symm).symm
  have hp : L.IsSymmetricProjection := ⟨hi, hs⟩
  have he := (LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hp).2
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_subspaceProjector]
  simpa only [hr] using he

lemma inverseRoot_normalization {ι : Type} [Fintype ι] [DecidableEq ι] (M : Op ι) (hM : M.PosSemidef) :
    cfc (fun x : ℝ => (Real.sqrt x)⁻¹) M * M *
      cfc (fun x : ℝ => (Real.sqrt x)⁻¹) M +
      subspaceProjector (LinearMap.ker (Matrix.toEuclideanLin M)) = 1 := by
  let f : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹
  let q : ℝ → ℝ := fun x => if x = 0 then 1 else 0
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ M) :=
    M.finite_real_spectrum.continuousOn g
  have hsa : IsSelfAdjoint M := hM.isHermitian
  have he : cfc f M * M * cfc f M = 1 - cfc q M := by
    calc
      _ = (cfc f M * cfc (fun x : ℝ => x) M) * cfc f M := by rw [cfc_id' ℝ M hsa]
      _ = cfc (fun x : ℝ => f x * x * f x) M := by
        rw [← cfc_mul f (fun x : ℝ => x) M (hc _) (hc _),
          ← cfc_mul (fun x : ℝ => f x * x) f M (hc _) (hc _)]
      _ = cfc (fun x : ℝ => 1 - q x) M := by
        apply cfc_congr
        intro x hx
        have hnonneg : 0 ≤ x := by
          rw [hM.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
          obtain ⟨j, rfl⟩ := hx
          exact hM.eigenvalues_nonneg j
        dsimp [f, q]
        split_ifs with hxzero
        · simp [hxzero]
        · have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne hnonneg (Ne.symm hxzero)))
          field_simp
          nlinarith [Real.sq_sqrt hnonneg]
      _ = 1 - cfc q M := by
        rw [cfc_sub (fun _ : ℝ => 1) q M (hc _) (hc _), cfc_const_one ℝ M hsa]
  change cfc f M * M * cfc f M + _ = 1
  rw [he, ← cfc_kernelProjector M hM.isHermitian]
  exact sub_add_cancel _ _

end RandomDimReduction.Channel

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma continuous_reduction_integrand (n k d : ℕ) (X : Op (Word n d)) :
    Continuous (fun V : Matrix.unitaryGroup (Fin d) ℂ =>
      (tensor n (randomEmbedding k V))ᴴ * inverseRootMoment n k d * X *
        inverseRootMoment n k d * tensor n (randomEmbedding k V)) := by
  have hT : Continuous (fun V : Matrix.unitaryGroup (Fin d) ℂ => tensor n (randomEmbedding k V)) :=
    (continuous_tensor_all n).comp (continuous_subtype_val.matrix_mul continuous_const)
  exact (((hT.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_const).matrix_mul continuous_const).matrix_mul hT

lemma reduction_add (n k d : ℕ) (X Y : Op (Word n d)) :
    reduction n k d (X + Y) = reduction n k d X + reduction n k d Y := by
  unfold reduction
  simp_rw [Matrix.mul_add, Matrix.add_mul]
  exact integral_add
    ((continuous_reduction_integrand n k d X).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((continuous_reduction_integrand n k d Y).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

lemma reduction_smul (n k d : ℕ) (r : ℂ) (X : Op (Word n d)) :
    reduction n k d (r • X) = r • reduction n k d X := by
  unfold reduction
  simp_rw [Matrix.mul_smul, Matrix.smul_mul]
  exact integral_smul _ _

lemma RTP_add (n k d : ℕ) (X Y : Op (Word n d)) :
    RTP n k d (X + Y) = RTP n k d X + RTP n k d Y := by
  simp only [RTP, reduction_add, Matrix.mul_add, Matrix.trace_add,
    add_div, add_smul]
  abel

lemma RTP_smul (n k d : ℕ) (r : ℂ) (X : Op (Word n d)) :
    RTP n k d (r • X) = r • RTP n k d X := by
  simp only [RTP, reduction_smul, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, mul_div_assoc, mul_smul, smul_add]

noncomputable def RTPLinearMap (n k d : ℕ) : Op (Word n d) →ₗ[ℂ] Op (Word n k) where
  toFun := RTP n k d
  map_add' := RTP_add n k d
  map_smul' := RTP_smul n k d

end RandomDimReduction.Channel

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma trace_reduction (n k d : ℕ) (X : Op (Word n d)) :
    (reduction n k d X).trace =
      (inverseRootMoment n k d * moment n k d * inverseRootMoment n k d * X).trace := by
  let A := inverseRootMoment n k d
  let T := fun V : Matrix.unitaryGroup (Fin d) ℂ => tensor n (randomEmbedding k V)
  have hT : Continuous T :=
    (continuous_tensor_all n).comp (continuous_subtype_val.matrix_mul continuous_const)
  have hf := (continuous_reduction_integrand n k d X).integrable_of_hasCompactSupport
    (μ := MixedCloning.Optimal.haar d) (HasCompactSupport.of_compactSpace _)
  have hM : moment n k d = ∫ V, T V * (T V)ᴴ ∂MixedCloning.Optimal.haar d := by
    unfold moment
    simp_rw [tensor_mul, tensor_conjTranspose]
    rfl
  let L : Op (Word n d) →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap (Word n d) ℂ ℂ).comp
      ((mulRightLinearMap (Word n d) ℂ X).comp
        ((mulRightLinearMap (Word n d) ℂ A).comp (mulLeftLinearMap (Word n d) ℂ A)))
  have hgram := (hT.matrix_mul hT.matrix_conjTranspose).integrable_of_hasCompactSupport
    (μ := MixedCloning.Optimal.haar d) (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ V, ((T V)ᴴ * A * X * A * T V).trace ∂MixedCloning.Optimal.haar d :=
      ((Matrix.traceLinearMap (Word n k) ℂ ℂ).toContinuousLinearMap.integral_comp_comm hf).symm
    _ = ∫ V, L (T V * (T V)ᴴ) ∂MixedCloning.Optimal.haar d := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro V
      change ((T V)ᴴ * A * X * A * T V).trace = (A * (T V * (T V)ᴴ) * A * X).trace
      calc
        _ = (T V * ((T V)ᴴ * A * X * A)).trace := Matrix.trace_mul_comm _ _
        _ = ((T V * (T V)ᴴ * A * X) * A).trace := by simp only [Matrix.mul_assoc]
        _ = (A * (T V * (T V)ᴴ * A * X)).trace := Matrix.trace_mul_comm _ _
        _ = _ := by simp only [Matrix.mul_assoc]
    _ = L (∫ V, T V * (T V)ᴴ ∂MixedCloning.Optimal.haar d) :=
      L.toContinuousLinearMap.integral_comp_comm hgram
    _ = _ := by rw [← hM]; rfl

lemma RTP_trace (n k d : ℕ) (hk : 1 ≤ k) (X : Op (Word n d)) :
    (RTP n k d X).trace = X.trace := by
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdim : (k ^ n : ℂ) ≠ 0 := pow_ne_zero n hkC
  have hn := inverseRoot_normalization (moment n k d) (moment_posSemidef n k d)
  change inverseRootMoment n k d * moment n k d * inverseRootMoment n k d +
    kernelProjector n k d = 1 at hn
  simp only [RTP, Matrix.trace_add, trace_reduction, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, smul_eq_mul]
  rw [div_mul_cancel₀ _ hdim, ← Matrix.trace_add, ← Matrix.add_mul, hn, Matrix.one_mul]

end RandomDimReduction.Channel

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

lemma integral_matrix_entry {a b G : Type} [Fintype a] [Fintype b]
    [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] (F : G → Matrix a b ℂ)
    (hF : Continuous F) (i : a) (j : b) :
    (∫ g, F g ∂μ) i j = ∫ g, F g i j ∂μ := by
  have hi := hF.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace F)
  exact ((Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap.integral_comp_comm hi).symm

lemma outputFirstChoi_apply {I O : Type} [Fintype I] [DecidableEq I]
    (M : Op I →ₗ[ℂ] Op O) (i j : O × I) :
    outputFirstChoi M i j = M (Matrix.single i.2 j.2 (1 : ℂ)) i.1 j.1 := by
  unfold outputFirstChoi QAlgorithms.Papers.Independent.Information100.P34.choi
  apply congrArg (fun X : Op I => M X i.1 j.1)
  ext a b
  simp [Matrix.single_apply]

lemma sandwich_single {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    (B : Matrix b a ℂ) (i j : a) (r s : b) :
    (B * Matrix.single i j (1 : ℂ) * Bᴴ) r s = B r i * star (B s j) := by
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

lemma choi_RTP_formula (n k d : ℕ) :
    outputFirstChoi (RTPLinearMap n k d) =
      (∫ V : Matrix.unitaryGroup (Fin d) ℂ,
        let B := (tensor n (randomEmbedding k V))ᴴ * inverseRootMoment n k d
        let v : Word n k × Word n d → ℂ := fun i => B i.1 i.2
        Matrix.vecMulVec v (star v)
        ∂MixedCloning.Optimal.haar d) +
      ((k ^ n : ℂ)⁻¹) • Matrix.kronecker (1 : Op (Word n k)) (kernelProjector n k d)ᵀ := by
  let A := inverseRootMoment n k d
  have hA : Aᴴ = A := inverseRootMoment_isHermitian n k d
  let F := fun V : Matrix.unitaryGroup (Fin d) ℂ =>
    let B := (tensor n (randomEmbedding k V))ᴴ * A
    let v : Word n k × Word n d → ℂ := fun i => B i.1 i.2
    Matrix.vecMulVec v (star v)
  have hT : Continuous (fun V : Matrix.unitaryGroup (Fin d) ℂ => tensor n (randomEmbedding k V)) :=
    (continuous_tensor_all n).comp (continuous_subtype_val.matrix_mul continuous_const)
  have hB := hT.matrix_conjTranspose.matrix_mul (continuous_const (y := A))
  have hF : Continuous F := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    dsimp [F, Matrix.vecMulVec]
    exact ((continuous_apply i.2).comp ((continuous_apply i.1).comp hB)).mul
      (((continuous_apply j.2).comp ((continuous_apply j.1).comp hB)).star)
  ext i j
  rw [Matrix.add_apply, integral_matrix_entry _ F hF]
  rw [outputFirstChoi_apply]
  change RTP n k d (Matrix.single i.2 j.2 (1 : ℂ)) i.1 j.1 = _
  simp only [RTP, Matrix.add_apply]
  congr 1
  · unfold reduction
    rw [integral_matrix_entry _ _ (continuous_reduction_integrand n k d _)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro V
    let B := (tensor n (randomEmbedding k V))ᴴ * A
    change ((tensor n (randomEmbedding k V))ᴴ * A * Matrix.single i.2 j.2 (1 : ℂ) * A *
      tensor n (randomEmbedding k V)) i.1 j.1 = B i.1 i.2 * star (B j.1 j.2)
    calc
      _ = (B * Matrix.single i.2 j.2 (1 : ℂ) * Bᴴ) i.1 j.1 := by
        dsimp [B]
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA]
        simp only [Matrix.mul_assoc]
      _ = _ := sandwich_single B i.2 j.2 i.1 j.1
  · simp [Matrix.trace_mul_single, Matrix.kronecker, Matrix.smul_apply,
      Matrix.transpose_apply, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

lemma RTP_completelyPositive (n k d : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    QAlgorithms.Entanglement.IsCompletelyPositive (RTPLinearMap n k d) := by
  letI : Nonempty (Word n k) := ⟨fun _ => ⟨0, by omega⟩⟩
  letI : Nonempty (Word n d) := ⟨fun _ => ⟨0, by omega⟩⟩
  apply (choi_completelyPositive (RTPLinearMap n k d)).mpr
  rw [choi_RTP_formula]
  apply Matrix.PosSemidef.add
  · apply integral_posSemidef
    · have hT : Continuous (fun V : Matrix.unitaryGroup (Fin d) ℂ => tensor n (randomEmbedding k V)) :=
        (continuous_tensor_all n).comp (continuous_subtype_val.matrix_mul continuous_const)
      have hB := hT.matrix_conjTranspose.matrix_mul (continuous_const (y := inverseRootMoment n k d))
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact ((continuous_apply i.2).comp ((continuous_apply i.1).comp hB)).mul
        (((continuous_apply j.2).comp ((continuous_apply j.1).comp hB)).star)
    · intro V
      exact Matrix.posSemidef_vecMulVec_self_star _
  · have hQ : (kernelProjector n k d).PosSemidef := subspaceProjector_posSemidef _
    have hK := (Matrix.PosSemidef.one (n := Word n k) (R := ℂ)).kronecker hQ.transpose
    exact hK.smul (by positivity)

end RandomDimReduction.Channel

open RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (n k d : ℕ) (hn : 0 < n) (hk : 1 ≤ k) (hkd : k ≤ d) :
    ∃ L : Op (Word n d) →ₗ[ℂ] Op (Word n k),
      (∀ X, L X = RTP n k d X) ∧ WildeQIT.EntBreaking.IsQuantumChannel L := by
  refine ⟨RTPLinearMap n k d, fun _ => rfl, ?_⟩
  exact ⟨RTP_completelyPositive n k d hk hkd, RTP_trace n k d hk⟩
