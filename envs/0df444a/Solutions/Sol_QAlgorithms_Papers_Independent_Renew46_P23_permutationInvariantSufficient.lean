-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P23.permutationInvariantSufficient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:34:45.299007+00:00
-- url     : https://prove2.me/submissions/049b9fe9-11d3-4ef7-a0e4-57049dadc74b

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P23
noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Renew46.P23

open QAlgorithms.Papers.Independent.Next46.P43
  (SufficientSigmaAlgebra MinimalSufficientSigmaAlgebra IsCStarCoarseGraining)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (relativeEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

local instance : MeasurableSpace Bool := ⊤

/-- precomposition with a permutation as an equivalence of index tuples -/
def g64m_eqv {I : Type*} {n : ℕ} (p : Equiv.Perm (Fin n)) : (Fin n → I) ≃ (Fin n → I) where
  toFun x := x ∘ p
  invFun x := x ∘ p.symm
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

lemma g64m_action_apply {I : Type*} (n : ℕ) (p : Equiv.Perm (Fin n))
    (A : Matrix (Fin n → I) (Fin n → I) ℂ) (x y : Fin n → I) :
    permutationAction n p A x y = A (x ∘ p) (y ∘ p) := rfl

lemma g64m_avg_apply {I : Type*} (n : ℕ)
    (A : Matrix (Fin n → I) (Fin n → I) ℂ) (x y : Fin n → I) :
    permutationAverage n A x y =
      (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ * ∑ p : Equiv.Perm (Fin n), A (x ∘ p) (y ∘ p) := by
  simp only [permutationAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  congr 1
  rw [Matrix.sum_apply]
  rfl

lemma g64m_avg_eq {I : Type*} (n : ℕ) (A : Matrix (Fin n → I) (Fin n → I) ℂ) :
    permutationAverage n A =
      ∑ p : Equiv.Perm (Fin n), (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ • permutationAction n p A := by
  simp only [permutationAverage, LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]

lemma g64m_action_mul {I : Type*} [Fintype I] (n : ℕ) (p : Equiv.Perm (Fin n))
    (A B : Matrix (Fin n → I) (Fin n → I) ℂ) :
    permutationAction n p (A * B) = permutationAction n p A * permutationAction n p B := by
  ext x y
  simp only [g64m_action_apply, Matrix.mul_apply]
  exact (Fintype.sum_equiv (g64m_eqv p) _ _ (fun z => rfl)).symm

lemma g64m_action_star {I : Type*} (n : ℕ) (p : Equiv.Perm (Fin n))
    (A : Matrix (Fin n → I) (Fin n → I) ℂ) :
    permutationAction n p (star A) = star (permutationAction n p A) := by
  ext x y
  rfl

lemma g64m_action_one {I : Type*} [DecidableEq I] (n : ℕ) (p : Equiv.Perm (Fin n)) :
    permutationAction n p (1 : Matrix (Fin n → I) (Fin n → I) ℂ) = 1 := by
  ext x y
  simp only [g64m_action_apply, Matrix.one_apply]
  have : x ∘ p = y ∘ p ↔ x = y := (g64m_eqv p).injective.eq_iff
  by_cases h : x = y
  · simp [h]
  · rw [if_neg (by rwa [this]), if_neg h]

lemma g64m_card_ne {n : ℕ} : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

lemma g64m_csum_apply {A ι : Type*} [AddCommMonoid A] (s : Finset ι)
    (f : ι → CStarMatrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    (∑ p ∈ s, f p) i j = ∑ p ∈ s, f p i j :=
  Matrix.sum_apply i j s f

lemma g64m_gen {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ)
    (b : CStarMatrix (Fin 2) (Fin 2) (Matrix (Fin n → I) (Fin n → I) ℂ)) :
    (star b * b).map (permutationAverage (I := I) n) =
        ∑ p : Equiv.Perm (Fin n),
          star ((((Real.sqrt (Fintype.card (Equiv.Perm (Fin n)) : ℝ))⁻¹ : ℝ) : ℂ) •
              b.map (permutationAction n p)) *
            ((((Real.sqrt (Fintype.card (Equiv.Perm (Fin n)) : ℝ))⁻¹ : ℝ) : ℂ) •
              b.map (permutationAction n p)) := by
  set c : ℂ := (((Real.sqrt (Fintype.card (Equiv.Perm (Fin n)) : ℝ))⁻¹ : ℝ) : ℂ) with hc
  have hcc : star c * c = (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ := by
    rw [hc, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
    push_cast; rfl
  have h1 : ∀ p : Equiv.Perm (Fin n), star (c • b.map (permutationAction n p)) *
      (c • b.map (permutationAction n p)) =
      (star c * c) • (star (b.map (permutationAction n p)) * b.map (permutationAction n p)) := by
    intro p
    rw [star_smul, CStarMatrix.smul_mul, CStarMatrix.mul_smul, smul_smul]
  simp only [h1, hcc]
  refine CStarMatrix.ext (fun i j => ?_)
  rw [CStarMatrix.map_apply, CStarMatrix.mul_apply, g64m_avg_eq]
  rw [g64m_csum_apply]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [CStarMatrix.smul_apply, CStarMatrix.mul_apply, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [g64m_action_mul, CStarMatrix.star_apply, CStarMatrix.star_apply, g64m_action_star,
    CStarMatrix.map_apply, CStarMatrix.map_apply]

theorem solution
    {I Theta : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (n : ℕ) (hn : 1 ≤ n)
    (rho : Theta → Matrix I I ℂ)
    (hRho : ∀ theta, QAlgorithms.IsDensityMatrix (rho theta)) :
    IsCStarCoarseGraining (permutationAverage (I := I) n) ∧
    (∀ (A : Matrix (Fin n → I) (Fin n → I) ℂ)
      (p : Equiv.Perm (Fin n)) (x y : Fin n → I),
      permutationAverage n A (x ∘ p) (y ∘ p) = permutationAverage n A x y) ∧
    (∀ theta (A : Matrix (Fin n → I) (Fin n → I) ℂ),
      (copies n (rho theta) * permutationAverage n A).trace =
        (copies n (rho theta) * A).trace) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · ext x y
    rw [g64m_avg_apply]
    have : ∀ p : Equiv.Perm (Fin n), (1 : Matrix (Fin n → I) (Fin n → I) ℂ) (x ∘ p) (y ∘ p)
        = (1 : Matrix (Fin n → I) (Fin n → I) ℂ) x y := fun p => by
      have h := congrFun (congrFun (g64m_action_one (I := I) n p) x) y
      exact (g64m_action_apply n p 1 x y).symm.trans h
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ g64m_card_ne, one_mul]
  · intro X hX
    rw [StarOrderedRing.nonneg_iff] at hX
    induction hX using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      rw [g64m_gen]
      exact Finset.sum_nonneg (fun p _ => star_mul_self_nonneg _)
    | zero =>
      have : (0 : CStarMatrix (Fin 2) (Fin 2) (Matrix (Fin n → I) (Fin n → I) ℂ)).map
          (permutationAverage (I := I) n) = 0 := CStarMatrix.ext (fun i j => by
            simp [CStarMatrix.map_apply, CStarMatrix.zero_apply])
      rw [this]
    | add x y _ _ hx hy =>
      have : (x + y).map (permutationAverage (I := I) n) =
          x.map (permutationAverage (I := I) n) + y.map (permutationAverage (I := I) n) :=
        CStarMatrix.ext (fun i j => by simp [CStarMatrix.map_apply])
      rw [this]
      exact add_nonneg hx hy
  · intro A p x y
    rw [g64m_avg_apply, g64m_avg_apply]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft p) _ _ (fun q => rfl)
  · intro theta A
    have hc : ∀ (p : Equiv.Perm (Fin n)) (x y : Fin n → I),
        copies n (rho theta) (x ∘ p) (y ∘ p) = copies n (rho theta) x y := by
      intro p x y
      simp only [copies, Matrix.of_apply, Function.comp]
      exact Fintype.prod_equiv p _ _ (fun i => rfl)
    have hp : ∀ p : Equiv.Perm (Fin n),
        (copies n (rho theta) * permutationAction n p A).trace = (copies n (rho theta) * A).trace := by
      intro p
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, g64m_action_apply]
      refine Fintype.sum_equiv (g64m_eqv p) _ _ (fun x => ?_)
      refine Fintype.sum_equiv (g64m_eqv p) _ _ (fun y => ?_)
      simp only [g64m_eqv, Equiv.coe_fn_mk, hc]
    rw [g64m_avg_eq]
    simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, hp,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, nsmul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ g64m_card_ne, one_mul]
