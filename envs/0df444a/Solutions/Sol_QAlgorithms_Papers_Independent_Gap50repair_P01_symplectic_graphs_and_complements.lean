-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap50repair.P01.symplectic_graphs_and_complements
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:39:38.933988+00:00
-- url     : https://prove2.me/submissions/65389f94-029f-4c87-8010-61f8df3e6be8

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01
noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

namespace X4CZD

attribute [local instance] Classical.propDecidable

lemma mem_graph {n : ℕ} (A : GroupedRealMatrix n) (x : (Coord n → ℝ) × (Coord n → ℝ)) :
    x ∈ graphSpace A ↔ x.2 = A *ᵥ x.1 := by
  unfold graphSpace
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨v, rfl⟩; simp [Matrix.toLin'_apply]
  · intro h; exact ⟨x.1, by ext <;> simp [Matrix.toLin'_apply, h]⟩

lemma finrank_graph {n : ℕ} (A : GroupedRealMatrix n) : Module.finrank ℝ (graphSpace A) = 2*n := by
  unfold graphSpace
  rw [LinearMap.finrank_range_of_inj]
  · simp [Module.finrank_fintype_fun_eq_card, two_mul]
  · intro v w h
    have := congrArg Prod.fst h
    simpa using this

lemma omegaR_eq {n : ℕ} (v w : Coord n → ℝ) : omegaR v w = v ⬝ᵥ (omegaMatrix n *ᵥ w) := by
  unfold omegaR omegaMatrix
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply,
    Finset.sum_sub_distrib]
  ring

lemma J_eq (n : ℕ) : canonicalJ n = -omegaMatrix n := by
  unfold canonicalJ omegaMatrix
  rw [Matrix.fromBlocks_neg]; simp

lemma symp_iff {n : ℕ} (A : GroupedRealMatrix n) :
    IsSymplectic A ↔ Aᵀ * omegaMatrix n * A = omegaMatrix n := by
  unfold IsSymplectic
  rw [J_eq, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

lemma form_zero {n : ℕ} (M : GroupedRealMatrix n) :
    (∀ v w : Coord n → ℝ, v ⬝ᵥ (M *ᵥ w) = 0) ↔ M = 0 := by
  constructor
  · intro h
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rw [Matrix.dotProduct_mulVec] at this
    simpa [Matrix.vecMul, dotProduct, Pi.single_apply] using this
  · rintro rfl v w; simp

lemma lag_iff {n : ℕ} (A : GroupedRealMatrix n) :
    IsGraphLagrangian (graphSpace A) ↔ IsSymplectic A := by
  unfold IsGraphLagrangian
  rw [finrank_graph, symp_iff]
  simp only [true_and]
  constructor
  · intro h
    rw [← sub_eq_zero, ← form_zero]
    intro v w
    have := h (v, A *ᵥ v) ((mem_graph A _).2 rfl) (w, A *ᵥ w) ((mem_graph A _).2 rfl)
    simp only [omegaR_eq] at this
    rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec v Aᵀ, Matrix.vecMul_transpose]
    linarith
  · intro h x hx y hy
    rw [mem_graph] at hx hy
    rw [hx, hy, omegaR_eq, omegaR_eq, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose A x.1,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h]
    ring

lemma compl_iff {n : ℕ} (A B : GroupedRealMatrix n) :
    IsCompl (graphSpace A) (graphSpace B) ↔ (A - B).det ≠ 0 := by
  rw [Submodule.isCompl_iff_disjoint]
  · rw [Submodule.disjoint_def, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro h ⟨v, hv, hAB⟩
      apply hv
      have := h (v, A *ᵥ v) ((mem_graph A _).2 rfl) ((mem_graph B _).2 (by
        rw [Matrix.sub_mulVec, sub_eq_zero] at hAB; exact hAB))
      exact congrArg Prod.fst this
    · intro h x hA hB
      rw [mem_graph] at hA hB
      by_contra hx
      apply h
      have h1 : x.1 ≠ 0 := by
        intro h1; apply hx; ext1
        · exact h1
        · rw [hA, h1, Matrix.mulVec_zero]; rfl
      exact ⟨x.1, h1, by rw [Matrix.sub_mulVec, ← hA, ← hB, sub_self]⟩
  · rw [finrank_graph, finrank_graph, Module.finrank_prod]
    simp [Module.finrank_fintype_fun_eq_card]; omega

lemma det_ne {n : ℕ} (A : GroupedRealMatrix n) (h : IsSymplectic A) : A.det ≠ 0 := by
  rw [symp_iff] at h
  have hO : (omegaMatrix n).det ≠ 0 := by
    have : omegaMatrix n * omegaMatrix n = -1 := by
      unfold omegaMatrix; rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
      simp
    intro h0
    have := congrArg Matrix.det this
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_neg, Matrix.det_one] at this
    simp at this
  intro h0
  apply hO
  rw [← h, Matrix.det_mul, h0, mul_zero]

theorem main {n : ℕ} :
    (∀ A : GroupedRealMatrix n, Module.finrank ℝ (graphSpace A) = 2*n ∧
      (IsGraphLagrangian (graphSpace A) ↔ IsSymplectic A)) ∧
    IsGraphLagrangian (graphSpace (1 : GroupedRealMatrix n)) ∧
    (∀ A : GroupedRealMatrix n, IsSymplectic A → IsGraphLagrangian (graphSpace (-A)) ∧
      IsCompl (graphSpace A) (graphSpace (-A))) ∧
    (∀ A B : GroupedRealMatrix n, IsCompl (graphSpace A) (graphSpace B) ↔ (A-B).det ≠ 0) := by
  refine ⟨fun A => ⟨finrank_graph A, lag_iff A⟩, (lag_iff 1).2 (by simp [IsSymplectic]),
    fun A hA => ⟨(lag_iff _).2 ?_, (compl_iff _ _).2 ?_⟩, compl_iff⟩
  · unfold IsSymplectic at *; simpa using hA
  · rw [sub_neg_eq_add, ← two_smul ℝ A, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (det_ne A hA)

end X4CZD

theorem solution {n : ℕ} :
    (∀ A : GroupedRealMatrix n, Module.finrank ℝ (graphSpace A) = 2*n ∧
      (IsGraphLagrangian (graphSpace A) ↔ IsSymplectic A)) ∧
    IsGraphLagrangian (graphSpace (1 : GroupedRealMatrix n)) ∧
    (∀ A : GroupedRealMatrix n, IsSymplectic A → IsGraphLagrangian (graphSpace (-A)) ∧
      IsCompl (graphSpace A) (graphSpace (-A))) ∧
    (∀ A B : GroupedRealMatrix n, IsCompl (graphSpace A) (graphSpace B) ↔ (A-B).det ≠ 0) :=
  X4CZD.main
