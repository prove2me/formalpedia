-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P31.otherParticleCuts
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:35:56.258574+00:00
-- url     : https://prove2.me/submissions/3205bf44-f2cf-46d3-8415-e6658e2b7b7d

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P31

noncomputable section

namespace P31Aux

open QAlgorithms QAlgorithms.Schur QAlgorithms.Papers.Independent.Dependency50.P31
open scoped ComplexConjugate

lemma act_apply {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) (y : ι) :
    act A ψ y = ∑ x, A y x * ψ x := by
  simp [act, Matrix.mulVec, dotProduct]

lemma act_act {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act A (act B ψ) = act (A * B) ψ := by
  simp [act, Matrix.mulVec_mulVec]

lemma toEuclideanLin_eq_act {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) : Matrix.toEuclideanLin A ψ = act A ψ := by
  rfl

lemma act_tp {d n : ℕ} (σ : Equiv.Perm (Fin n)) (ψ : EuclideanSpace ℂ (Fin n → Fin d))
    (y : Fin n → Fin d) : act (tensorPermutation d n σ) ψ y = ψ (y ∘ σ) := by
  rw [act_apply]
  rw [Finset.sum_eq_single (y ∘ σ)]
  · simp [tensorPermutation, Function.comp_assoc]
  · intro x _ hx
    have : ¬ (y = x ∘ σ.symm) := by
      rintro rfl; apply hx; ext i; simp
    simp [tensorPermutation, this]
  · simp

lemma tp_mul {d n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    tensorPermutation d n σ * tensorPermutation d n τ = tensorPermutation d n (σ * τ) := by
  ext y x
  simp only [tensorPermutation, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (x ∘ τ.symm)]
  · simp only [ite_true]
    rfl
  · intro z _ hz; simp [hz]
  · simp


/-- relabel by left multiplication -/
def relab {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    EuclideanSpace ℂ (Equiv.Perm (Fin n)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Equiv.Perm (Fin n)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.mulLeft σ)

lemma relab_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : EuclideanSpace ℂ (Equiv.Perm (Fin n)))
    (g : Equiv.Perm (Fin n)) : relab σ v g = v (σ⁻¹ * g) := by
  rfl

lemma relab_ket {n : ℕ} (σ : Equiv.Perm (Fin n)) (g : Equiv.Perm (Fin n)) :
    relab σ (ket g) = ket (σ * g) := by
  ext h
  rw [relab_apply]
  simp [ket, inv_mul_eq_iff_eq_mul]

lemma relab_young {d n : ℕ} (lambda : Partition d n) (σ : Equiv.Perm (Fin n))
    (v : EuclideanSpace ℂ (Equiv.Perm (Fin n))) :
    relab σ (Matrix.toEuclideanLin (youngRightOperator lambda) v) =
      Matrix.toEuclideanLin (youngRightOperator lambda) (relab σ v) := by
  ext g
  rw [relab_apply]
  simp only [Matrix.toEuclideanLin_apply, PiLp.toLp_apply, Matrix.mulVec, dotProduct]
  simp_rw [relab_apply]
  symm
  rw [← Equiv.sum_comp (Equiv.mulLeft σ)]
  apply Finset.sum_congr rfl
  intro h _
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
  congr 1
  simp only [youngRightOperator, Matrix.of_apply, inv_mul_eq_iff_eq_mul, mul_assoc]

lemma map_relab {d n : ℕ} (lambda : Partition d n) (σ : Equiv.Perm (Fin n)) :
    (spechtSpace lambda).map ((relab σ).toLinearEquiv : _ →ₗ[ℂ] _) = spechtSpace lambda := by
  have hle : ∀ τ : Equiv.Perm (Fin n), ∀ x ∈ spechtSpace lambda, relab τ x ∈ spechtSpace lambda := by
    intro τ x hx
    obtain ⟨v, rfl⟩ := hx
    exact ⟨relab τ v, (relab_young lambda τ v).symm⟩
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hle σ x hx
  · intro x hx
    refine ⟨relab σ⁻¹ x, hle σ⁻¹ x hx, ?_⟩
    ext g
    change relab σ (relab σ⁻¹ x) g = x g
    rw [relab_apply, relab_apply]
    simp

lemma proj_inv {d n : ℕ} (lambda : Partition d n) (σ a b : Equiv.Perm (Fin n)) :
    spechtProjection lambda (σ * a) (σ * b) = spechtProjection lambda a b := by
  simp only [spechtProjection, Matrix.of_apply]
  rw [← relab_ket, ← relab_ket]
  have := Submodule.starProjection_map_apply (relab σ) (spechtSpace lambda) (relab σ (ket b))
  simp only [map_relab] at this
  rw [this, LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map]

lemma char_eq {d n : ℕ} (lambda : Partition d n) (π : Equiv.Perm (Fin n)) :
    spechtCharacter lambda π = ∑ g, spechtProjection lambda (π⁻¹ * g) g := by
  simp only [spechtCharacter, Matrix.trace, Matrix.diag, Matrix.mul_apply, leftRegular,
    Matrix.of_apply, ite_mul, one_mul, zero_mul]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_eq_single (π⁻¹ * g)]
  · simp
  · intro h _ hh
    have : ¬ g = π * h := by rintro rfl; simp at hh
    simp [this]
  · simp

lemma char_conj {d n : ℕ} (lambda : Partition d n) (σ π : Equiv.Perm (Fin n)) :
    spechtCharacter lambda (σ⁻¹ * π * σ) = spechtCharacter lambda π := by
  rw [char_eq, char_eq]
  rw [← Equiv.sum_comp (Equiv.mulLeft σ⁻¹)]
  apply Finset.sum_congr rfl
  intro g _
  simp only [Equiv.coe_mulLeft]
  rw [show (σ⁻¹ * π * σ)⁻¹ * (σ⁻¹ * g) = σ⁻¹ * (π⁻¹ * g) by group, proj_inv]


lemma iso_comm {d n : ℕ} (nu : Partition d n) (σ : Equiv.Perm (Fin n)) :
    tensorPermutation d n σ * isotypicProjector nu = isotypicProjector nu * tensorPermutation d n σ := by
  unfold isotypicProjector
  rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  simp_rw [Matrix.mul_smul, Matrix.smul_mul, tp_mul]
  rw [← Equiv.sum_comp ((Equiv.mulRight σ).trans (Equiv.mulLeft σ⁻¹))]
  apply Finset.sum_congr rfl
  intro ρ _
  simp only [Equiv.trans_apply, Equiv.coe_mulRight, Equiv.coe_mulLeft]
  rw [show (σ⁻¹ * (ρ * σ))⁻¹ = σ⁻¹ * ρ⁻¹ * σ by group, char_conj,
    show σ * (σ⁻¹ * (ρ * σ)) = ρ * σ by group]

lemma tp_mem {d n : ℕ} (nu : Partition d n) (σ : Equiv.Perm (Fin n)) (ψ : H d n)
    (hψ : ψ ∈ isotypicSpace nu) : act (tensorPermutation d n σ) ψ ∈ isotypicSpace nu := by
  obtain ⟨v, rfl⟩ := hψ
  refine ⟨act (tensorPermutation d n σ) v, ?_⟩
  rw [toEuclideanLin_eq_act, toEuclideanLin_eq_act, act_act, act_act, iso_comm]

lemma tp_norm {d n : ℕ} (σ : Equiv.Perm (Fin n)) (ψ : H d n) :
    ‖act (tensorPermutation d n σ) ψ‖ = ‖ψ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp_rw [act_tp]
  let e : (Fin n → Fin d) ≃ (Fin n → Fin d) :=
    ⟨fun y => y ∘ σ, fun y => y ∘ σ.symm, fun y => by ext i; simp, fun y => by ext i; simp⟩
  exact Equiv.sum_comp e (fun y => ‖ψ y‖ ^ 2)

lemma swap_invol {d n : ℕ} (k l : Fin n) (ψ : H d n) :
    act (tensorPermutation d n (Equiv.swap k l)) (act (tensorPermutation d n (Equiv.swap k l)) ψ) = ψ := by
  ext y
  rw [act_tp, act_tp]
  rw [show (y ∘ ⇑(Equiv.swap k l)) ∘ ⇑(Equiv.swap k l) = y from by ext i; simp]

lemma cont_lss {d n : ℕ} : Continuous (fun ψ : H d n => largestSchmidtSq ψ) := by
  unfold largestSchmidtSq specNorm
  let _ := @Matrix.instL2OpNormedAddCommGroup ℂ (Fin d) (Fin d) _ _ _ _
  apply continuous_norm.comp
  have : Continuous (fun ψ : H d n => (lastMarginal ψ : Matrix (Fin d) (Fin d) ℂ)) := by
    unfold lastMarginal
    apply continuous_pi; intro a; apply continuous_pi; intro b
    apply continuous_finsetSum; intro x _
    exact ((PiLp.continuous_apply 2 _ _).mul (Complex.continuous_conj.comp (PiLp.continuous_apply 2 _ _)))
  exact this

lemma bdd {d n : ℕ} (U : Submodule ℂ (H d n)) :
    BddAbove {r : ℝ | ∃ psi ∈ U, ‖psi‖ = 1 ∧ r = largestSchmidtSq psi} := by
  apply ((isCompact_sphere (0 : H d n) 1).image cont_lss).bddAbove.mono
  rintro r ⟨psi, -, h1, rfl⟩
  exact ⟨psi, by simpa using h1, rfl⟩

end P31Aux

open QAlgorithms QAlgorithms.Schur QAlgorithms.Papers.Independent.Dependency50.P31
open scoped ComplexConjugate
open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] Classical.propDecidable

theorem solution {d n : ℕ} (hn : 2 ≤ n) (nu : Schur.Partition d n)
    (k : Fin n) (hk : k.val ≠ n-1) (psi : H d n)
    (hpsi : psi ∈ isotypicSpace nu) (hunit : ‖psi‖ = 1)
    (hmax : largestSchmidtSq psi = subspaceOptimum (isotypicSpace nu)) :
    swapToLast (by omega) k psi ∈ isotypicSpace nu ∧
    ‖swapToLast (by omega) k psi‖ = 1 ∧
    specNorm (particleMarginal (by omega) k (swapToLast (by omega) k psi)) =
      subspaceOptimum (isotypicSpace nu) ∧
    (∀ phi ∈ isotypicSpace nu, ‖phi‖ = 1 →
      specNorm (particleMarginal (by omega) k phi) ≤
        specNorm (particleMarginal (by omega) k (swapToLast (by omega) k psi))) := by
  have h3 : specNorm (particleMarginal (by omega) k (swapToLast (by omega) k psi)) =
      subspaceOptimum (isotypicSpace nu) := by
    rw [← hmax]
    unfold particleMarginal swapToLast
    rw [P31Aux.swap_invol]
    rfl
  refine ⟨P31Aux.tp_mem nu _ psi hpsi, by unfold swapToLast; rw [P31Aux.tp_norm, hunit], h3, ?_⟩
  intro phi hphi hphi1
  rw [h3]
  apply le_csSup (P31Aux.bdd _)
  refine ⟨swapToLast (by omega) k phi, P31Aux.tp_mem nu _ phi hphi, ?_, rfl⟩
  unfold swapToLast; rw [P31Aux.tp_norm, hphi1]
