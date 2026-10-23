-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P16.tangency_lazySubspace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T00:58:44.947584+00:00
-- url     : https://prove2.me/submissions/35f06481-34c0-4816-b62b-0c74d51bbd27

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

lemma X7TG_rates_nonneg {n r : ℕ} (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) : 0 ≤ rates V U i j :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma X7TG_pg_mulVec {n r : ℕ} (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ)
    (x : Fin n → ℝ) (i : Fin n) (hi : x i = 0) :
    (populationGenerator V U *ᵥ x) i = ∑ j, rates V U i j * x j := by
  simp only [populationGenerator, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal, hi,
    mul_zero, sub_zero]
  rfl

/-- the block-zero frame exists -/
lemma X7TG_frame {n : ℕ} (D : LindbladData n) (F : Face n) (x : Fin n → ℝ) (hx : x ∈ faceInterior F)
    (A : RMat n) (hA : A ∈ convexHull ℝ (fields D)) (ht : A *ᵥ x ∈ faceTangent F) :
    ∃ U, specialUnitary U ∧ ∀ i ∉ F.support, ∀ j ∈ F.support, rates D.jump U i j = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨⟨⟨hx0, _⟩, hxF⟩, hxpos⟩ := hx
  let f : RMat n → ℝ := fun B => ∑ i ∈ F.supportᶜ, (B *ᵥ x) i
  have hlin : IsLinearMap ℝ f := by
    constructor
    · intro B C
      simp only [f, Matrix.add_mulVec, Pi.add_apply, Finset.sum_add_distrib]
    · intro c B
      simp only [f, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  have hconv : Convex ℝ {B | 0 < f B} := convex_halfSpace_gt hlin 0
  have hsub : fields D ⊆ {B | 0 < f B} := by
    rintro B ⟨U, hU, rfl⟩
    obtain ⟨i, hi, j, hj, hr⟩ := hne U hU
    show 0 < ∑ i ∈ F.supportᶜ, (populationGenerator D.jump U *ᵥ x) i
    have hterm : ∀ i ∈ F.supportᶜ, 0 ≤ (populationGenerator D.jump U *ᵥ x) i := by
      intro i hi
      rw [X7TG_pg_mulVec _ _ _ _ (hxF i (Finset.mem_compl.mp hi))]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (X7TG_rates_nonneg _ _ _ _) (hx0 j)
    refine Finset.sum_pos' hterm ⟨i, Finset.mem_compl.mpr hi, ?_⟩
    rw [X7TG_pg_mulVec _ _ _ _ (hxF i hi)]
    refine Finset.sum_pos' (fun j _ => mul_nonneg (X7TG_rates_nonneg _ _ _ _) (hx0 j))
      ⟨j, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (X7TG_rates_nonneg _ _ _ _) (Ne.symm hr))
        (hxpos j hj)⟩
  have hAf := convexHull_min hsub hconv hA
  have h0 : f A = 0 := Finset.sum_eq_zero fun i hi => ht.2 i (Finset.mem_compl.mp hi)
  simp only [Set.mem_ofPred_eq] at hAf
  linarith


lemma X7TG_act_single {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    QAlgorithms.act W (EuclideanSpace.single j 1) = ∑ i, W i j • EuclideanSpace.single i 1 := by
  ext l
  simp [QAlgorithms.act, Pi.single_apply]

lemma X7TG_act_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    QAlgorithms.act A (QAlgorithms.act B v) = QAlgorithms.act (A * B) v := by
  simp [QAlgorithms.act, Matrix.mulVec_mulVec]

lemma X7TG_subspace {n r : ℕ} (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (F : Face n)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : specialUnitary U)
    (h0 : ∀ i ∉ F.support, ∀ j ∈ F.support, rates V U i j = 0) :
    ∃ S : Submodule ℂ (EuclideanSpace ℂ (Fin n)), lazy V S ∧ Module.finrank ℂ S = F.support.card := by
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU.1
  have h2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU.1
  have hW : ∀ k, ∀ i ∉ F.support, ∀ j ∈ F.support, (Uᴴ * V k * U) i j = 0 := by
    intro k i hi j hj
    have := h0 i hi j hj
    unfold rates at this
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)] at this
    exact Complex.normSq_eq_zero.mp (this k (Finset.mem_univ _))
  let b : F.support → EuclideanSpace ℂ (Fin n) := fun j => QAlgorithms.act U (EuclideanSpace.single j.1 1)
  have hinj : LinearMap.ker (Matrix.toEuclideanLin U) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro v w hvw
    have := congrArg (QAlgorithms.act Uᴴ) hvw
    change QAlgorithms.act Uᴴ (QAlgorithms.act U v) = QAlgorithms.act Uᴴ (QAlgorithms.act U w) at this
    simpa [X7TG_act_mul, h1, QAlgorithms.act] using this
  have hli : LinearIndependent ℂ b := by
    have h := ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis.linearIndependent.comp
      (Subtype.val : F.support → Fin n) Subtype.val_injective).map' (Matrix.toEuclideanLin U) hinj
    have hb : b = (Matrix.toEuclideanLin U) ∘ (EuclideanSpace.basisFun (Fin n) ℂ).toBasis ∘
        (Subtype.val : F.support → Fin n) := by
      funext j
      simp only [b, Function.comp, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
      rfl
    rw [hb]; exact h
  refine ⟨Submodule.span ℂ (Set.range b), ⟨?_, ?_⟩, ?_⟩
  · intro hbot
    obtain ⟨j, hj⟩ := F.nonempty
    have : b ⟨j, hj⟩ ∈ Submodule.span ℂ (Set.range b) := Submodule.subset_span ⟨_, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    exact hli.ne_zero ⟨j, hj⟩ this
  · rintro X ⟨k, rfl⟩ v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      have e : V k * U = U * (Uᴴ * V k * U) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
      simp only [b]
      rw [X7TG_act_mul, e, ← X7TG_act_mul, X7TG_act_single]
      change Matrix.toEuclideanLin U _ ∈ _
      rw [map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_smul]
      by_cases hi : i ∈ F.support
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
      · rw [hW k i hi j.1 j.2, zero_smul]
        exact Submodule.zero_mem _
    | zero =>
      change Matrix.toEuclideanLin (V k) 0 ∈ _
      rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      change Matrix.toEuclideanLin (V k) (x + y) ∈ _
      rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      change Matrix.toEuclideanLin (V k) (a • x) ∈ _
      rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · rw [finrank_span_eq_card hli]
    simp

end QAlgorithms.Papers.Independent.Dependency50.P16

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Dependency50.P16 in
theorem solution {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (F : Face n) (x : (fun n : ℕ => Fin n → ℝ) n) (hx : x ∈ faceInterior F) (A : RMat n)
    (hA : A ∈ convexHull ℝ (fields D)) (ht : A *ᵥ x ∈ faceTangent F) :
    ∃ S : Submodule ℂ ((fun n : ℕ => EuclideanSpace ℂ (Fin n)) n), lazy D.jump S ∧
      Module.finrank ℂ S = F.support.card := by
  obtain ⟨U, hU, h0⟩ := X7TG_frame D F x hx A hA ht
  exact X7TG_subspace D.jump F U hU h0
