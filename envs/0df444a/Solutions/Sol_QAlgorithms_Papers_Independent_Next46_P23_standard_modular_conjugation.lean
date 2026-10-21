-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P23.standard_modular_conjugation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T22:38:28.570095+00:00
-- url     : https://prove2.me/submissions/caa7d89a-f528-4b14-b381-525f055dcb23

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

theorem g64d_psd_of_nonneg {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ)
    (hq : ∀ v : n → ℂ, 0 ≤ star v ⬝ᵥ (M *ᵥ v)) : M.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ hq
  rw [← Matrix.isSymmetric_toEuclideanLin_iff, LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  have h := hq (WithLp.ofLp v)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp]
  have him := (Complex.nonneg_iff.mp h).2
  have e : v.ofLp ⬝ᵥ star (M *ᵥ v.ofLp) = star (star v.ofLp ⬝ᵥ M *ᵥ v.ofLp) := by
    simp only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
  rw [e]
  apply Complex.ext <;> simp; rw [← him]; simp

theorem g64d_psd_of_dual (xi : Mat I)
    (h : ∀ eta : Mat I, eta.PosSemidef → (xiᴴ*eta).trace.im = 0 ∧ 0 ≤ (xiᴴ*eta).trace.re) :
    xi.PosSemidef := by
  have hx : (xiᴴ).PosSemidef := by
    refine g64d_psd_of_nonneg _ ?_
    · intro v
      have := h (Matrix.vecMulVec v (star v)) (Matrix.posSemidef_vecMulVec_self_star v)
      rw [g64d_tr_vmv] at this
      exact Complex.nonneg_iff.mpr ⟨this.2, this.1.symm⟩
  simpa using hx.conjTranspose

theorem solution [Nonempty I] :
    ((∀ xi eta : Mat I, ∀ c : ℂ, (xi+eta)ᴴ = xiᴴ + etaᴴ ∧
      (c • xi)ᴴ = conj c • xiᴴ ∧ (xiᴴ)ᴴ = xi ∧
      (xiᴴ * eta).trace = conj (((xiᴴ)ᴴ * etaᴴ).trace)) ∧
      (∀ xi : Mat I, QAlgorithms.frobNorm (xiᴴ) = QAlgorithms.frobNorm xi)) ∧
    (conjugateByJ '' Set.range (leftMatrix : Mat I → Mat (I × I)) =
      matrixCommutant (Set.range (leftMatrix : Mat I → Mat (I × I)))) ∧
    (∀ xi : Mat I, xi.PosSemidef ↔
      ∀ eta : Mat I, eta.PosSemidef → (xiᴴ*eta).trace.im = 0 ∧ 0 ≤ (xiᴴ*eta).trace.re) ∧
    (∀ xi : Mat I, xi.PosSemidef → xiᴴ = xi) ∧
    (∀ X : Mat (I × I), X ∈ Set.range (leftMatrix : Mat I → Mat (I × I)) →
      X ∈ matrixCommutant (Set.range (leftMatrix : Mat I → Mat (I × I))) → conjugateByJ X = Xᴴ) ∧
    (∀ A xi : Mat I, xi.PosSemidef → (A * (A*xi)ᴴ).PosSemidef) := by
  refine ⟨⟨fun xi eta c => ⟨Matrix.conjTranspose_add _ _, ?_, Matrix.conjTranspose_conjTranspose _, ?_⟩,
    fun xi => ?_⟩, ?_, fun xi => ⟨fun hxi eta heta => ?_, g64d_psd_of_dual xi⟩,
    fun xi hxi => hxi.1.eq, ?_, fun A xi hxi => ?_⟩
  · rw [Matrix.conjTranspose_smul]; rfl
  · change _ = star _
    rw [Matrix.conjTranspose_conjTranspose, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
  · exact Matrix.frobenius_norm_conjTranspose xi
  · rw [g64d_commutant_L]
    ext X
    constructor
    · rintro ⟨_, ⟨A, rfl⟩, rfl⟩; exact ⟨A, (g64d_J_L A).symm⟩
    · rintro ⟨A, rfl⟩; exact ⟨leftMatrix A, ⟨A, rfl⟩, g64d_J_L A⟩
  · rw [hxi.1.eq]
    have := Complex.nonneg_iff.mp (g64d_tr_psd xi eta hxi heta)
    exact ⟨this.2.symm, this.1⟩
  · rintro X ⟨A, rfl⟩ hX
    have hc : ∀ B : Mat I, B * A = A * B := by
      intro B
      have h1 := hX (leftMatrix B) ⟨B, rfl⟩
      obtain ⟨j0⟩ := ‹Nonempty I›
      ext i k
      have := congrFun (congrFun h1 (i, j0)) (k, j0)
      simp [Matrix.mul_apply, leftMatrix, Fintype.sum_prod_type] at this
      simpa [Matrix.mul_apply] using this.symm
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr
      (fun i j => hc (Matrix.single i j 1))
    subst hc
    ext x y
    simp [conjugateByJ, leftMatrix, Matrix.scalar_apply, Matrix.diagonal_apply]
    congr 1; by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;> simp [h1, h2, eq_comm]
  · rw [Matrix.conjTranspose_mul, hxi.1.eq, ← Matrix.mul_assoc]
    exact hxi.mul_mul_conjTranspose_same A
