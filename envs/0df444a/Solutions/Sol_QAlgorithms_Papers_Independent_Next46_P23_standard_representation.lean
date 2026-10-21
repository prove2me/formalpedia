-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P23.standard_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T22:44:53.465979+00:00
-- url     : https://prove2.me/submissions/e9befbe6-00b5-4a40-babc-876046d67861

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23
noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

open QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem g64d_LR_entry_comm (A B : Mat I) :
    leftMatrix A * rightMatrix B = rightMatrix B * leftMatrix A := by
  ext x y
  simp only [Matrix.mul_apply, leftMatrix, rightMatrix, Fintype.sum_prod_type]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

theorem g64d_comm_L (X : Mat (I × I)) [Nonempty I]
    (h : ∀ A : Mat I, X * leftMatrix A = leftMatrix A * X) : ∃ B : Mat I, X = rightMatrix B := by
  obtain ⟨i0⟩ := ‹Nonempty I›
  have key : ∀ i j k l, X (i, j) (k, l) = if i = k then X (i0, j) (i0, l) else 0 := by
    intro i j k l
    have := congrFun (congrFun (h (Matrix.single k i0 1)) (i, j)) (i0, l)
    simp only [Matrix.mul_apply, leftMatrix, Fintype.sum_prod_type, Matrix.single_apply] at this
    simp [ite_and, mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq'] at this
    by_cases hik : i = k
    · subst hik; simp only [if_true]; simpa [eq_comm] using this
    · simp only [hik, if_false]
      simpa [Ne.symm hik, hik] using this
  refine ⟨fun j l => conj (X (i0, j) (i0, l)), ?_⟩
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [key]
  simp [rightMatrix]

theorem g64d_comm_R (X : Mat (I × I)) [Nonempty I]
    (h : ∀ A : Mat I, X * rightMatrix A = rightMatrix A * X) : ∃ B : Mat I, X = leftMatrix B := by
  obtain ⟨i0⟩ := ‹Nonempty I›
  have key : ∀ i j k l, X (i, j) (k, l) = if j = l then X (i, i0) (k, i0) else 0 := by
    intro i j k l
    have := congrFun (congrFun (h (Matrix.single l i0 1)) (i, j)) (k, i0)
    simp only [Matrix.mul_apply, rightMatrix, Fintype.sum_prod_type, Matrix.single_apply] at this
    simp [ite_and, mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq'] at this
    by_cases hjl : j = l
    · subst hjl; simp only [if_true]; simpa [eq_comm] using this
    · simp only [hjl, if_false]
      simpa [Ne.symm hjl, hjl] using this
  refine ⟨fun i k => X (i, i0) (k, i0), ?_⟩
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [key]
  simp [leftMatrix]

theorem g64d_commutant_L [Nonempty I] :
    matrixCommutant (Set.range (leftMatrix : Mat I → Mat (I × I))) = Set.range rightMatrix := by
  ext X
  constructor
  · intro hX
    obtain ⟨B, hB⟩ := g64d_comm_L X (fun A => hX _ ⟨A, rfl⟩)
    exact ⟨B, hB.symm⟩
  · rintro ⟨B, rfl⟩ Y ⟨A, rfl⟩
    exact (g64d_LR_entry_comm A B).symm

theorem g64d_commutant_R [Nonempty I] :
    matrixCommutant (Set.range (rightMatrix : Mat I → Mat (I × I))) = Set.range leftMatrix := by
  ext X
  constructor
  · intro hX
    obtain ⟨B, hB⟩ := g64d_comm_R X (fun A => hX _ ⟨A, rfl⟩)
    exact ⟨B, hB.symm⟩
  · rintro ⟨B, rfl⟩ Y ⟨A, rfl⟩
    exact g64d_LR_entry_comm B A

theorem g64d_J_L (A : Mat I) : conjugateByJ (leftMatrix A) = rightMatrix A := by
  ext x y
  simp only [conjugateByJ, leftMatrix, rightMatrix]
  split_ifs <;> simp

theorem g64d_tr_vmv (P : Mat I) (v : I → ℂ) :
    (P * Matrix.vecMulVec v (star v)).trace = star v ⬝ᵥ P *ᵥ v := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply]; ring

theorem g64d_tr_psd (P Q : Mat I) (hP : P.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hQ
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [g64d_tr_vmv]
  exact hP.dotProduct_mulVec_nonneg _

theorem g64d_L_one : leftMatrix (1 : Mat I) = 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩; simp only [leftMatrix, Matrix.one_apply, Prod.mk.injEq]; split_ifs <;> simp_all

theorem g64d_R_one : rightMatrix (1 : Mat I) = 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩; simp only [rightMatrix, Matrix.one_apply, Prod.mk.injEq]; split_ifs <;> simp_all

theorem g64d_L_add (A B : Mat I) : leftMatrix (A + B) = leftMatrix A + leftMatrix B := by
  ext x y; simp only [leftMatrix, Matrix.add_apply]; split_ifs <;> simp

theorem g64d_R_add (A B : Mat I) : rightMatrix (A + B) = rightMatrix A + rightMatrix B := by
  ext x y; simp [rightMatrix, mul_add]

theorem g64d_L_smul (c : ℂ) (A : Mat I) : leftMatrix (c • A) = c • leftMatrix A := by
  ext x y; simp [leftMatrix, mul_assoc]; try ring

theorem g64d_R_smul (c : ℂ) (A : Mat I) : rightMatrix (c • A) = conj c • rightMatrix A := by
  ext x y; simp [rightMatrix]; try ring

theorem g64d_L_mul (A B : Mat I) : leftMatrix (A * B) = leftMatrix A * leftMatrix B := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.mul_apply, leftMatrix, Fintype.sum_prod_type]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_mul]

theorem g64d_R_mul (A B : Mat I) : rightMatrix (A * B) = rightMatrix A * rightMatrix B := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.mul_apply, rightMatrix, Fintype.sum_prod_type]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mul_sum, map_sum]

theorem g64d_L_star (A : Mat I) : leftMatrix (Aᴴ) = (leftMatrix A)ᴴ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [leftMatrix, Matrix.conjTranspose_apply]; split_ifs <;> simp_all

theorem g64d_R_star (A : Mat I) : rightMatrix (Aᴴ) = (rightMatrix A)ᴴ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [rightMatrix, Matrix.conjTranspose_apply]; split_ifs <;> simp_all

theorem g64d_L_inj [Nonempty I] : Function.Injective (leftMatrix : Mat I → Mat (I × I)) := by
  intro A B h
  obtain ⟨j0⟩ := ‹Nonempty I›
  ext i k
  simpa [leftMatrix] using congrFun (congrFun h (i, j0)) (k, j0)

theorem g64d_R_inj [Nonempty I] : Function.Injective (rightMatrix : Mat I → Mat (I × I)) := by
  intro A B h
  obtain ⟨i0⟩ := ‹Nonempty I›
  ext j l
  have := congrFun (congrFun h (i0, j)) (i0, l)
  simp [rightMatrix] at this
  exact star_injective this

noncomputable def g64d_Lhom : Mat I →⋆ₐ[ℂ] Mat (I × I) where
  toFun := leftMatrix
  map_one' := g64d_L_one
  map_mul' := g64d_L_mul
  map_zero' := by ext x y; simp [leftMatrix]
  map_add' := g64d_L_add
  commutes' := fun c => by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [g64d_L_smul, g64d_L_one]
  map_star' := g64d_L_star

noncomputable def g64d_Rhom : Mat I →⋆ₐ[ℂ] Mat (I × I) where
  toFun := fun A => rightMatrix (A.map star)
  map_one' := by simp [g64d_R_one]
  map_mul' := fun A B => by
    rw [← g64d_R_mul]; congr 1; ext i j; simp [Matrix.mul_apply, map_sum]
  map_zero' := by ext x y; simp [rightMatrix]
  map_add' := fun A B => by rw [← g64d_R_add]; congr 1; ext; simp
  commutes' := fun c => by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [show (c • (1 : Mat I)).map star = conj c • 1 by
      ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]; split_ifs <;> simp,
      g64d_R_smul, g64d_R_one]
    simp
  map_star' := fun A => by
    show rightMatrix _ = (rightMatrix _)ᴴ
    rw [← g64d_R_star]; congr 1

theorem g64d_norm_conj_le (B : Mat I) : ‖B.map star‖ ≤ ‖B‖ := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have h := Matrix.l2_opNorm_mulVec B (WithLp.toLp 2 (star x.ofLp))
  have e1 : ‖(Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) (B.map star) x‖ =
      ‖(EuclideanSpace.equiv I ℂ).symm (B *ᵥ (WithLp.toLp 2 (star x.ofLp)).ofLp)‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← norm_star (((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) (B.map star) x) i)]
    rw [Matrix.ofLp_toEuclideanCLM]
    simp [Matrix.mulVec, dotProduct, star_sum]
  have e2 : ‖(WithLp.toLp 2 (star x.ofLp) : EuclideanSpace ℂ I)‖ = ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp
  rw [e1]; rw [e2] at h; exact h

theorem g64d_norm_conj (A : Mat I) : ‖A.map star‖ = ‖A‖ := by
  refine le_antisymm (g64d_norm_conj_le A) ?_
  have := g64d_norm_conj_le (A.map star)
  rwa [Matrix.map_map, show (star ∘ star : ℂ → ℂ) = id from funext fun z => star_star z,
    Matrix.map_id] at this

theorem g64d_single_LR (i j k l : I) :
    Matrix.single ((i, j) : I × I) ((k, l) : I × I) (1 : ℂ) =
      leftMatrix (Matrix.single i k 1) * rightMatrix (Matrix.single j l 1) := by
  ext ⟨a, b⟩ ⟨c, e⟩
  simp only [Matrix.mul_apply, leftMatrix, rightMatrix, Fintype.sum_prod_type, Matrix.single_apply]
  simp only [Prod.mk.injEq]
  by_cases h1 : i = a <;> by_cases h2 : j = b <;> by_cases h3 : k = c <;> by_cases h4 : l = e <;>
    simp [h1, h2, h3, h4, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]

theorem g64d_scalar_eq (c : ℂ) : (Matrix.scalar I c : Mat I) = c • (1 : Mat I) := by
  ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

theorem solution [Nonempty I] :
    ((∀ A : Mat I, QAlgorithms.specNorm (leftMatrix A) = QAlgorithms.specNorm A ∧
      QAlgorithms.specNorm (rightMatrix A) = QAlgorithms.specNorm A) ∧
      Function.Injective (leftMatrix : Mat I → Mat (I × I)) ∧
      Function.Injective (rightMatrix : Mat I → Mat (I × I))) ∧
    (leftMatrix (1 : Mat I) = 1 ∧ rightMatrix (1 : Mat I) = 1 ∧
      ∀ A B : Mat I, ∀ c : ℂ,
      leftMatrix (A+B) = leftMatrix A + leftMatrix B ∧
      rightMatrix (A+B) = rightMatrix A + rightMatrix B ∧
      leftMatrix (c • A) = c • leftMatrix A ∧ rightMatrix (c • A) = conj c • rightMatrix A ∧
      leftMatrix (A*B) = leftMatrix A * leftMatrix B ∧
      rightMatrix (A*B) = rightMatrix A * rightMatrix B ∧
      leftMatrix (Aᴴ) = (leftMatrix A)ᴴ ∧ rightMatrix (Aᴴ) = (rightMatrix A)ᴴ) ∧
    (Set.range (leftMatrix : Mat I → Mat (I × I)) ∩ Set.range (rightMatrix : Mat I → Mat (I × I)) =
      {X | ∃ c : ℂ, X = c • 1}) ∧
    (StarAlgebra.adjoin ℂ (Set.range (leftMatrix : Mat I → Mat (I × I)) ∪
      Set.range (rightMatrix : Mat I → Mat (I × I))) = ⊤) ∧
    (matrixCommutant (Set.range (leftMatrix : Mat I → Mat (I × I))) = Set.range rightMatrix) ∧
    (matrixCommutant (Set.range (rightMatrix : Mat I → Mat (I × I))) = Set.range leftMatrix) := by
  refine ⟨⟨fun A => ⟨?_, ?_⟩, g64d_L_inj, g64d_R_inj⟩,
    ⟨g64d_L_one, g64d_R_one, fun A B c => ⟨g64d_L_add A B, g64d_R_add A B, g64d_L_smul c A,
      g64d_R_smul c A, g64d_L_mul A B, g64d_R_mul A B, g64d_L_star A, g64d_R_star A⟩⟩,
    ?_, ?_, g64d_commutant_L, g64d_commutant_R⟩
  · exact NonUnitalStarAlgHom.norm_map (g64d_Lhom (I := I)) g64d_L_inj A
  · have hinj : Function.Injective (g64d_Rhom (I := I)) := by
      intro X Y h
      have h' : rightMatrix (X.map star) = rightMatrix (Y.map star) := h
      have := g64d_R_inj h'
      ext i j
      exact star_injective (congrFun (congrFun this i) j)
    have e : rightMatrix A = g64d_Rhom (A.map star) := by
      show rightMatrix A = rightMatrix ((A.map star).map star)
      congr 1; ext i j; simp
    show ‖rightMatrix A‖ = ‖A‖
    rw [e, NonUnitalStarAlgHom.norm_map (g64d_Rhom (I := I)) hinj, g64d_norm_conj]
  · ext X
    constructor
    · rintro ⟨⟨A, rfl⟩, ⟨B, hB⟩⟩
      have hc : ∀ C : Mat I, C * A = A * C := by
        intro C
        apply g64d_L_inj
        rw [g64d_L_mul, g64d_L_mul, ← hB, g64d_LR_entry_comm]
      obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr
        (fun i j => hc (Matrix.single i j 1))
      refine ⟨c, ?_⟩
      rw [← hc, g64d_scalar_eq, g64d_L_smul, g64d_L_one]
    · rintro ⟨c, rfl⟩
      refine ⟨⟨c • 1, by rw [g64d_L_smul, g64d_L_one]⟩, ⟨conj c • 1, ?_⟩⟩
      rw [g64d_R_smul, g64d_R_one]; simp
  · refine eq_top_iff.mpr fun X _ => ?_
    rw [Matrix.matrix_eq_sum_single X]
    refine sum_mem fun p _ => sum_mem fun q _ => ?_
    rw [show Matrix.single p q (X p q) = X p q • Matrix.single p q 1 by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]]
    refine (StarAlgebra.adjoin ℂ (Set.range (leftMatrix : Mat I → Mat (I × I)) ∪
      Set.range (rightMatrix : Mat I → Mat (I × I)))).smul_mem ?_ _
    obtain ⟨i, j⟩ := p
    obtain ⟨k, l⟩ := q
    rw [g64d_single_LR]
    exact mul_mem (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨_, rfl⟩))
      (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨_, rfl⟩))
