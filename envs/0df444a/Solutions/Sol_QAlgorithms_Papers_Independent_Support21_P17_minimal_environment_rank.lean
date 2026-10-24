-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P17.minimal_environment_rank
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T04:42:01.179391+00:00
-- url     : https://prove2.me/submissions/72dce3d8-a319-4af8-b778-56d16f2b63f0

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17


noncomputable section
open scoped ComplexConjugate TensorProduct Matrix ComplexOrder
set_option linter.unusedSectionVars false

namespace QAlgorithms.Papers.Independent.Support21.P17
namespace X8ME
open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

theorem gram_rank {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (w : ι → F) :
    (Matrix.of fun a b => inner ℂ (w a) (w b)).rank =
      Module.finrank ℂ (Submodule.span ℂ (Set.range w)) := by
  let b := stdOrthonormalBasis ℂ F
  let L : F ≃ₗ[ℂ] (Fin (Module.finrank ℂ F) → ℂ) :=
    b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℂ _)
  let B : Matrix (Fin (Module.finrank ℂ F)) ι ℂ := Matrix.of fun k a => L (w a) k
  have hG : (Matrix.of fun a c => inner ℂ (w a) (w c)) = Bᴴ * B := by
    ext a c
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, B, L]
    rw [← b.repr.inner_map_map (w a) (w c), PiLp.inner_apply]
    simp [RCLike.inner_apply, mul_comm]
  rw [hG, Matrix.rank_conjTranspose_mul_self, Matrix.rank_eq_finrank_span_cols]
  have hr : Set.range B.col = L '' Set.range w := by
    rw [← Set.range_comp]; rfl
  rw [hr, show (⇑L '' Set.range w) = (L.toLinearMap) '' Set.range w from rfl,
    Submodule.span_image, LinearEquiv.finrank_map_eq]

theorem rank_smul_ne {I : Type*} [Fintype I] (c : ℂ) (hc : c ≠ 0) (A : Matrix I I ℂ) :
    (c • A).rank = A.rank := by
  unfold Matrix.rank
  have : (c • A).mulVecLin = c • A.mulVecLin := by
    ext v; simp
  rw [this, LinearMap.range_smul _ _ hc]

section CT
variable {H N : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]

abbrev ιc (H N : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup N] [InnerProductSpace ℂ N] : (H ⊗[ℂ] N) →L[ℂ] NoiseSpace H N :=
  UniformSpace.Completion.toComplL

theorem ctm_coe (A : H →L[ℂ] H) (B : N →L[ℂ] N) (t : H ⊗[ℂ] N) :
    completedTensorMap A B (ιc H N t) = ιc H N (TensorProduct.mapL A B t) := by
  unfold completedTensorMap
  rw [ContinuousLinearMap.extend_eq]
  · rfl
  · rw [UniformSpace.Completion.coe_toComplL]; exact UniformSpace.Completion.denseRange_coe
  · rw [UniformSpace.Completion.coe_toComplL]; exact UniformSpace.Completion.isUniformInducing_coe _

theorem ext_coe {f g : NoiseSpace H N →L[ℂ] NoiseSpace H N}
    (h : ∀ t, f (ιc H N t) = g (ιc H N t)) : f = g := by
  ext z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq f.continuous g.continuous
  | ih t => exact h t

theorem ctm_add (A A' : H →L[ℂ] H) (B : N →L[ℂ] N) :
    completedTensorMap (A + A') B = completedTensorMap A B + completedTensorMap A' B := by
  apply ext_coe; intro t
  rw [ContinuousLinearMap.add_apply, ctm_coe, ctm_coe, ctm_coe, ← map_add]
  congr 1
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.add_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]; abel

theorem ctm_smul (c : ℂ) (A : H →L[ℂ] H) (B : N →L[ℂ] N) :
    completedTensorMap (c • A) B = c • completedTensorMap A B := by
  apply ext_coe; intro t
  rw [ContinuousLinearMap.smul_apply, ctm_coe, ctm_coe, ← map_smul]
  congr 1
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

theorem ctm_zero (B : N →L[ℂ] N) : completedTensorMap (0 : H →L[ℂ] H) B = 0 := by
  have := ctm_smul (0 : ℂ) (0 : H →L[ℂ] H) B
  simpa using this

theorem ctm_sum {κ : Type*} (s : Finset κ) (A : κ → H →L[ℂ] H) (B : N →L[ℂ] N) :
    completedTensorMap (∑ k ∈ s, A k) B = ∑ k ∈ s, completedTensorMap (A k) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ctm_zero]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, ctm_add, ih]

end CT
end X8ME
end QAlgorithms.Papers.Independent.Support21.P17


noncomputable section
open scoped ComplexConjugate TensorProduct Matrix ComplexOrder
set_option linter.unusedSectionVars false

namespace QAlgorithms.Papers.Independent.Support21.P17
namespace X8ME
open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

variable {m : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

abbrev EH (m : ℕ) := EuclideanSpace ℂ (Fin m)

def ee (i : Fin m) : EH m := EuclideanSpace.single i 1

def psi (m : ℕ) (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    (Fin m → F) →ₗ[ℂ] (EH m ⊗[ℂ] F) :=
  ∑ i, (TensorProduct.mk ℂ (EH m) F (ee i)) ∘ₗ LinearMap.proj i

theorem psi_apply (y : Fin m → F) : psi m F y = ∑ i, ee i ⊗ₜ[ℂ] y i := by
  simp [psi]

theorem eh_sum (x : EH m) : x = ∑ i, x.ofLp i • ee i := by
  ext j
  simp [ee, Pi.single_apply]

theorem psi_tmul (x : EH m) (f : F) : x ⊗ₜ[ℂ] f = psi m F (fun i => x.ofLp i • f) := by
  rw [psi_apply]
  conv_lhs => rw [eh_sum x]
  rw [TensorProduct.sum_tmul]
  simp [TensorProduct.smul_tmul]

theorem psi_surj (t : EH m ⊗[ℂ] F) : ∃ y, psi m F y = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul x f => exact ⟨_, (psi_tmul x f).symm⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb]⟩

def mop (B : Matrix (Fin m) (Fin m) ℂ) : EH m →L[ℂ] EH m :=
  (Matrix.toEuclideanLin B).toContinuousLinearMap

theorem mop_ee (B : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) :
    mop B (ee i) = ∑ k, B k i • ee k := by
  ext j
  simp [mop, ee, EuclideanSpace.single_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem mapL_psi (B : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → F) :
    TensorProduct.mapL (mop B) (ContinuousLinearMap.id ℂ F) (psi m F y) =
      psi m F (fun k => ∑ i, B k i • y i) := by
  rw [psi_apply, psi_apply, map_sum]
  simp only [TensorProduct.mapL_tmul, mop_ee, ContinuousLinearMap.id_apply, TensorProduct.sum_tmul,
    TensorProduct.tmul_sum, TensorProduct.smul_tmul]
  exact Finset.sum_comm

theorem inner_ee (i j : Fin m) : inner ℂ (ee i) (ee j) = if i = j then (1 : ℂ) else 0 := by
  simp [ee, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, eq_comm]

theorem inner_psi (y y' : Fin m → F) :
    inner ℂ (ιc (EH m) F (psi m F y)) (ιc (EH m) F (psi m F y')) = ∑ i, inner ℂ (y i) (y' i) := by
  rw [UniformSpace.Completion.coe_toComplL, UniformSpace.Completion.inner_coe, psi_apply, psi_apply]
  simp only [sum_inner, inner_sum, TensorProduct.inner_tmul, inner_ee]
  simp

theorem mop_linear_sum (A : Matrix (Fin m) (Fin m) ℂ) :
    mop A = ∑ i, ∑ j, A i j • mop (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [mop, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

end X8ME
end QAlgorithms.Papers.Independent.Support21.P17


noncomputable section
open scoped ComplexConjugate TensorProduct Matrix ComplexOrder
set_option linter.unusedSectionVars false

namespace QAlgorithms.Papers.Independent.Support21.P17
namespace X8ME
open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

variable {m n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

abbrev CC (m : ℕ) (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : Matrix (Fin m) (Fin m) ℂ) : NoiseSpace (EH m) F →L[ℂ] NoiseSpace (EH m) F :=
  completedTensorMap (mop A) (ContinuousLinearMap.id ℂ F)

theorem CC_expand (A : Matrix (Fin m) (Fin m) ℂ) :
    CC m F A = ∑ i, ∑ j, A i j • CC m F (Matrix.single i j 1) := by
  simp only [CC]
  rw [mop_linear_sum A, ctm_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ctm_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ctm_smul]

theorem CC_psi (A : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → F) :
    CC m F A (ιc (EH m) F (psi m F y)) = ιc (EH m) F (psi m F (fun k => ∑ i, A k i • y i)) := by
  rw [CC, ctm_coe, mapL_psi]

theorem fd_noise (V : EH n →L[ℂ] NoiseSpace (EH m) F)
    (h2 : (Submodule.span ℂ {z : NoiseSpace (EH m) F | ∃ A : Matrix (Fin m) (Fin m) ℂ, ∃ eta : EH n,
      z = CC m F A (V eta)}).topologicalClosure = ⊤) :
    FiniteDimensional ℂ (NoiseSpace (EH m) F) := by
  let g : Fin m × Fin m × Fin n → NoiseSpace (EH m) F :=
    fun p => CC m F (Matrix.single p.1 p.2.1 1) (V (ee p.2.2))
  have hle : Submodule.span ℂ {z : NoiseSpace (EH m) F | ∃ A : Matrix (Fin m) (Fin m) ℂ, ∃ eta : EH n,
      z = CC m F A (V eta)} ≤ Submodule.span ℂ (Set.range g) := by
    rw [Submodule.span_le]
    rintro z ⟨A, eta, rfl⟩
    rw [CC_expand A, eh_sum eta]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j, k), rfl⟩))
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range g)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
  have hcl : IsClosed (Submodule.span ℂ (Set.range g) : Set (NoiseSpace (EH m) F)) :=
    Submodule.closed_of_finiteDimensional _
  have htop : Submodule.span ℂ (Set.range g) = ⊤ := by
    rw [eq_top_iff, ← h2]
    exact Submodule.topologicalClosure_minimal _ hle hcl
  rw [htop] at this
  exact Submodule.topEquiv.finiteDimensional

theorem ι_surj [FiniteDimensional ℂ (NoiseSpace (EH m) F)] (z : NoiseSpace (EH m) F) :
    ∃ y : Fin m → F, ιc (EH m) F (psi m F y) = z := by
  have hc : IsClosed (LinearMap.range (ιc (EH m) F).toLinearMap : Set (NoiseSpace (EH m) F)) :=
    Submodule.closed_of_finiteDimensional _
  have hd : DenseRange (ιc (EH m) F) := by
    rw [UniformSpace.Completion.coe_toComplL]; exact UniformSpace.Completion.denseRange_coe
  have : z ∈ (LinearMap.range (ιc (EH m) F).toLinearMap : Set (NoiseSpace (EH m) F)) := by
    rw [← hc.closure_eq]
    exact hd.closure_range ▸ Set.mem_univ z
  obtain ⟨t, rfl⟩ := this
  obtain ⟨y, rfl⟩ := psi_surj t
  exact ⟨y, rfl⟩

theorem mop_entry (B : Matrix (Fin m) (Fin m) ℂ) (μ ν : Fin m) :
    inner ℂ (ee μ) (mop B (ee ν)) = B μ ν := by
  rw [mop_ee, inner_sum]
  simp [inner_smul_right, inner_ee]

end X8ME
end QAlgorithms.Papers.Independent.Support21.P17


noncomputable section
open scoped ComplexConjugate TensorProduct Matrix ComplexOrder
set_option linter.unusedSectionVars false

namespace QAlgorithms.Papers.Independent.Support21.P17
namespace X8ME
open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)
open QAlgorithms.Papers.Independent.Information100.P50 (M Lin)

variable {m n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem span_top_of (hm : 0 < m) (V : EH n →L[ℂ] NoiseSpace (EH m) F)
    [FiniteDimensional ℂ (NoiseSpace (EH m) F)]
    (h2 : (Submodule.span ℂ {z : NoiseSpace (EH m) F | ∃ A : Matrix (Fin m) (Fin m) ℂ, ∃ eta : EH n,
      z = CC m F A (V eta)}).topologicalClosure = ⊤)
    (y : Fin n → Fin m → F) (hy : ∀ ν, ιc (EH m) F (psi m F (y ν)) = V (ee ν)) :
    Submodule.span ℂ (Set.range fun p : Fin n × Fin m => y p.1 p.2) = ⊤ := by
  set W := Submodule.span ℂ (Set.range fun p : Fin n × Fin m => y p.1 p.2) with hWdef
  let P : (Fin m → W) →ₗ[ℂ] NoiseSpace (EH m) F :=
    ((ιc (EH m) F).toLinearMap ∘ₗ psi m F) ∘ₗ (LinearMap.pi fun i => W.subtype ∘ₗ LinearMap.proj i)
  have hP : ∀ u, P u = ιc (EH m) F (psi m F (fun i => (u i : F))) := fun u => rfl
  have hcl : IsClosed (LinearMap.range P : Set (NoiseSpace (EH m) F)) :=
    Submodule.closed_of_finiteDimensional _
  have hmemW : ∀ ν i, y ν i ∈ W := fun ν i => Submodule.subset_span ⟨(ν, i), rfl⟩
  have hle : Submodule.span ℂ {z : NoiseSpace (EH m) F | ∃ A : Matrix (Fin m) (Fin m) ℂ, ∃ eta : EH n,
      z = CC m F A (V eta)} ≤ LinearMap.range P := by
    rw [Submodule.span_le]
    rintro z ⟨A, eta, rfl⟩
    have hV : V eta = ιc (EH m) F (psi m F (∑ ν, eta.ofLp ν • y ν)) := by
      conv_lhs => rw [eh_sum eta]
      simp only [map_sum, map_smul, hy]
    rw [hV, CC_psi]
    refine ⟨fun k => ⟨∑ i, A k i • (∑ ν, eta.ofLp ν • y ν) i, ?_⟩, ?_⟩
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (by
        rw [Finset.sum_apply]
        exact Submodule.sum_mem _ fun ν _ => Submodule.smul_mem _ _ (hmemW ν i))
    · rw [hP]
  have hall : ∀ z : NoiseSpace (EH m) F, z ∈ LinearMap.range P := by
    intro z
    have : (⊤ : Submodule ℂ _) ≤ LinearMap.range P := by
      rw [← h2]; exact Submodule.topologicalClosure_minimal _ hle hcl
    exact this Submodule.mem_top
  rw [eq_top_iff]
  intro x _
  let i0 : Fin m := ⟨0, hm⟩
  obtain ⟨u, hu⟩ := hall (ιc (EH m) F (ee i0 ⊗ₜ[ℂ] x))
  rw [hP] at hu
  have hinj : psi m F (fun i => (u i : F)) = ee i0 ⊗ₜ[ℂ] x := by
    have := hu
    simp only [ιc, UniformSpace.Completion.coe_toComplL] at this
    exact UniformSpace.Completion.coe_injective _ this
  let Λ : (EH m ⊗[ℂ] F) →ₗ[ℂ] (F ⧸ W) :=
    (TensorProduct.lid ℂ (F ⧸ W)).toLinearMap ∘ₗ
      TensorProduct.map (EuclideanSpace.proj i0 : EH m →L[ℂ] ℂ).toLinearMap W.mkQ
  have hΛ : ∀ (a : EH m) (f : F), Λ (a ⊗ₜ[ℂ] f) = a.ofLp i0 • W.mkQ f := by
    intro a f; simp [Λ]
  have h1 := congrArg Λ hinj
  rw [psi_apply, map_sum] at h1
  simp only [hΛ, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 (u _).2, smul_zero,
    Finset.sum_const_zero] at h1
  have h3 : W.mkQ x = 0 := by
    rw [h1]; simp [ee]
  exact (Submodule.Quotient.mk_eq_zero W).1 h3

end X8ME
end QAlgorithms.Papers.Independent.Support21.P17


noncomputable section
open scoped ComplexConjugate TensorProduct Matrix ComplexOrder
set_option linter.unusedSectionVars false

namespace QAlgorithms.Papers.Independent.Support21.P17
namespace X8ME
open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)
open QAlgorithms.Papers.Independent.Information100.P50 (M Lin)

variable {m n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem kron_gram {ι : Type*} [Fintype ι] [DecidableEq ι] [FiniteDimensional ℂ F] (w : ι → F)
    (hw : Submodule.span ℂ (Set.range w) = ⊤) :
    (Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ) (Matrix.of fun a b => inner ℂ (w a) (w b))).rank =
      m * Module.finrank ℂ F := by
  let u : Fin m × ι → PiLp 2 (fun _ : Fin m => F) := fun p => WithLp.toLp 2 (Pi.single p.1 (w p.2))
  have hK : Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ) (Matrix.of fun a b => inner ℂ (w a) (w b)) =
      Matrix.of fun p q => inner ℂ (u p) (u q) := by
    ext p q
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.of_apply, u, PiLp.inner_apply,
      Matrix.one_apply]
    by_cases h : p.1 = q.1
    · rw [if_pos h, one_mul, Finset.sum_eq_single p.1]
      · simp [h]
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
    · rw [if_neg h, zero_mul]
      refine (Finset.sum_eq_zero fun b _ => ?_).symm
      by_cases hb : b = p.1
      · subst hb; simp [Pi.single_apply, Ne.symm h]
      · simp [Pi.single_apply, hb]
  have hu : Submodule.span ℂ (Set.range u) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    let ℓ : Fin m → F →ₗ[ℂ] PiLp 2 (fun _ : Fin m => F) := fun i =>
      (WithLp.linearEquiv 2 ℂ (Fin m → F)).symm.toLinearMap ∘ₗ LinearMap.single ℂ (fun _ : Fin m => F) i
    have hv : v = ∑ i, ℓ i (v.ofLp i) := by
      ext j; simp [ℓ, Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hmem : v.ofLp i ∈ Submodule.span ℂ (Set.range w) := hw ▸ Submodule.mem_top
    have : Submodule.map (ℓ i) (Submodule.span ℂ (Set.range w)) ≤ Submodule.span ℂ (Set.range u) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨(i, a), rfl⟩
    exact this ⟨_, hmem, rfl⟩
  rw [hK, gram_rank, hu, finrank_top, (WithLp.linearEquiv 2 ℂ (Fin m → F)).finrank_eq,
    Module.finrank_pi_fintype]
  simp

theorem main_gen (hm : 0 < m) (T : Lin m n) (V : EH n →L[ℂ] NoiseSpace (EH m) F)
    (h1 : ∀ A, mop (T A) = compress V (CC m F A))
    (h2 : (Submodule.span ℂ {z : NoiseSpace (EH m) F | ∃ A : Matrix (Fin m) (Fin m) ℂ, ∃ eta : EH n,
      z = CC m F A (V eta)}).topologicalClosure = ⊤) :
    FiniteDimensional ℂ F ∧ Module.finrank ℂ F = matrixRank (scaledChoi T) ∧
      m * Module.finrank ℂ F = matrixRank (tracialDerivative T) := by
  haveI := fd_noise V h2
  choose y hy using fun ν : Fin n => ι_surj (V (ee ν))
  have hT : ∀ A μ ν, T A μ ν = inner ℂ (V (ee μ)) (CC m F A (V (ee ν))) := by
    intro A μ ν
    rw [← mop_entry (T A) μ ν, h1]
    simp [compress, ContinuousLinearMap.adjoint_inner_right]
  let w : Fin n × Fin m → F := fun p => y p.1 p.2
  have hG : scaledChoi T = (m : ℂ) • Matrix.of fun a b => inner ℂ (w a) (w b) := by
    ext p q
    simp only [scaledChoi, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    congr 1
    rw [hT, ← hy, ← hy, CC_psi, inner_psi]
    simp only [Matrix.single_apply, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_eq_single p.2 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp [w]
  have hW := span_top_of hm V h2 y hy
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range w)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range w)
  have hFD : FiniteDimensional ℂ F := by
    have h := hW
    change Submodule.span ℂ (Set.range w) = ⊤ at h
    rw [h] at this
    exact Submodule.topEquiv.finiteDimensional
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨hFD, ?_, ?_⟩
  · unfold matrixRank
    change _ = (scaledChoi T).rank
    rw [hG, rank_smul_ne _ hm0, gram_rank]
    change _ = Module.finrank ℂ (Submodule.span ℂ (Set.range w))
    rw [show Submodule.span ℂ (Set.range w) = ⊤ from hW, finrank_top]
  · unfold matrixRank
    change _ = (tracialDerivative T).rank
    rw [tracialDerivative, hG, Matrix.kronecker, Matrix.kronecker_smul, rank_smul_ne _ hm0]
    exact (kron_gram w hW).symm

end X8ME

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)
open QAlgorithms.Papers.Independent.Information100.P50 (M Lin)

theorem x8_main (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (T : Lin m n) (hT : Entanglement.IsCompletelyPositive T)
    (E : SeparableHilbertSpace) (V : finiteHilbert n →L[ℂ] NoiseSpace (finiteHilbert m) E)
    (hV : IsMatrixCanonical T E V) :
    FiniteDimensional ℂ E ∧ Module.finrank ℂ E = matrixRank (scaledChoi T) ∧
      m * Module.finrank ℂ E = matrixRank (tracialDerivative T) :=
  X8ME.main_gen (F := E) hm T V hV.1 hV.2

end QAlgorithms.Papers.Independent.Support21.P17


open QAlgorithms.Papers.Independent.Support21.P17 in
theorem solution (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (T : QAlgorithms.Papers.Independent.Information100.P50.Lin m n)
    (hT : QAlgorithms.Entanglement.IsCompletelyPositive T)
    (E : SeparableHilbertSpace)
    (V : finiteHilbert n →L[ℂ] QAlgorithms.Papers.Independent.Claimed50.P50.NoiseSpace (finiteHilbert m) E)
    (hV : IsMatrixCanonical T E V) :
    FiniteDimensional ℂ E ∧ Module.finrank ℂ E = matrixRank (scaledChoi T) ∧
      m * Module.finrank ℂ E = matrixRank (tracialDerivative T) :=
  x8_main m n hm hn T hT E V hV
