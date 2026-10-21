-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P17.replica_covariance_relabeling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:43:01.646599+00:00
-- url     : https://prove2.me/submissions/cd799e93-345e-4721-bec3-e993de0e6013

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

theorem g58d_term {d : ℕ} (R : ReplicationChoiArray d) (U : (Matrix.unitaryGroup (Fin d) ℂ)) (i j : Fin d) :
    Matrix.trace (replica R U i j *
      Matrix.kronecker (measurementEffect U i) (measurementEffect U j)) =
    ∑ k, ((representation U)ᴴ * diagonalBlocks R i j k * representation U) ((i,j),k) ((i,j),k) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, replica, Matrix.kronecker, Matrix.kroneckerMap_apply,
    measurementEffect, representation, diagonalBlocks, Matrix.conjTranspose_apply, Matrix.map_apply,
    Finset.sum_mul, Fintype.sum_prod_type, star_mul', RCLike.star_def, Complex.conj_conj]
  simp only [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv
    { toFun := fun p : Fin d × Fin d × Fin d × Fin d × Fin d × Fin d × Fin d =>
        (p.2.2.2.2.1, p.1, p.2.1, p.2.2.2.2.2.2, p.2.2.1, p.2.2.2.1, p.2.2.2.2.2.1)
      invFun := fun q : Fin d × Fin d × Fin d × Fin d × Fin d × Fin d × Fin d =>
        (q.2.1, q.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1, q.1, q.2.2.2.2.2.2, q.2.2.2.1)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  intro x
  simp only [Equiv.coe_fn_mk]; ring

theorem g58d_rep_unitary {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    (representation U)ᴴ * representation U = 1 := by
  have h1 : (U : Op (Fin d))ᴴ * (U : Op (Fin d)) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have h2 : ((U : Op (Fin d)).map conj)ᴴ * (U : Op (Fin d)).map conj = 1 := by
    ext a b
    have := congrFun (congrFun h1 a) b
    have h3 := congrArg conj this
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul, RCLike.star_def,
      Complex.conj_conj, Matrix.one_apply] at h3
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, RCLike.star_def,
      Complex.conj_conj, Matrix.one_apply, h3]
    split_ifs <;> simp
  have m1 : (U : Op (Fin d)).map conj ∈ unitary (Matrix (Fin d) (Fin d) ℂ) :=
    Matrix.mem_unitaryGroup_iff'.mpr h2
  have m2 : (U : Op (Fin d)) ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := U.2
  have m3 := Matrix.kronecker_mem_unitary (Matrix.kronecker_mem_unitary m1 m1) m2
  exact Unitary.star_mul_self_of_mem m3

theorem g58d_si_cov {d : ℕ} (R : ReplicationChoiArray d) (hCov : BlocksCommuteWithRotations (diagonalBlocks R))
    (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    scoreIntegrand R U = (1 / (d : ℝ)^2) * ∑ i, ∑ j, ∑ k,
      (diagonalBlocks R i j k ((i,j),k) ((i,j),k)).re := by
  unfold scoreIntegrand
  congr 1
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [g58d_term, Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mul_assoc, hCov U i j k, ← Matrix.mul_assoc, g58d_rep_unitary, Matrix.one_mul]

theorem g58d_score_cov {d : ℕ} (R : ReplicationChoiArray d) (hCov : BlocksCommuteWithRotations (diagonalBlocks R)) :
    haarReplicationScore R = (1 / (d : ℝ)^2) * ∑ i, ∑ j, ∑ k,
      (diagonalBlocks R i j k ((i,j),k) ((i,j),k)).re := by
  unfold haarReplicationScore
  simp only [g58d_si_cov R hCov]
  rw [integral_const]
  have hu : QAlgorithms.Schur.unitaryHaar d Set.univ = 1 := Measure.haarMeasure_self
  simp [Measure.real, hu]

theorem g58d_perm_mem {d : ℕ} (τ : Equiv.Perm (Fin d)) :
    permutationMatrix τ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, permutationMatrix, Matrix.star_apply, Matrix.one_apply]
  have hh : ∀ x, (b = τ x) ↔ (x = τ.symm b) := by
    intro x; constructor <;> intro h <;> subst h <;> simp
  simp only [hh, Finset.sum_ite_eq', Finset.mem_univ, if_true, Equiv.apply_symm_apply]
  split_ifs <;> simp_all

theorem g58d_perm_cov {d : ℕ} (M : Op (ABC d)) (τ : Equiv.Perm (Fin d))
    (h : M * representation ⟨_, g58d_perm_mem τ⟩ = representation ⟨_, g58d_perm_mem τ⟩ * M)
    (a b : ABC d) : M ((τ a.1.1, τ a.1.2), τ a.2) ((τ b.1.1, τ b.1.2), τ b.2) = M a b := by
  have := congrFun (congrFun h ((τ a.1.1, τ a.1.2), τ a.2)) b
  simp only [Matrix.mul_apply, representation, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.map_apply, permutationMatrix, Fintype.sum_prod_type] at this
  simp [apply_ite, Finset.sum_ite_eq, Finset.sum_ite_eq'] at this
  exact this

theorem g58d_rep_unitary' {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    representation U * (representation U)ᴴ = 1 :=
  mul_eq_one_comm.mp (g58d_rep_unitary U)

theorem g58d_slice {d : ℕ} (W : (Matrix.unitaryGroup (Fin d) ℂ)) (M : Op (ABC d))
    (hc : M * representation W = representation W * M) (k : Fin d) (x y : AB d) :
    ∑ c, ∑ e, conj ((W : Op (Fin d)) c k) * M (y, c) (x, e) * (W : Op (Fin d)) e k =
    ∑ a : AB d, ∑ b : AB d, conj ((W : Op (Fin d)) y.1 a.1) * conj ((W : Op (Fin d)) y.2 a.2) *
      M (a, k) (b, k) * ((W : Op (Fin d)) x.1 b.1 * (W : Op (Fin d)) x.2 b.2) := by
  have h1 : (W : Op (Fin d))ᴴ * (W : Op (Fin d)) = 1 := Matrix.mem_unitaryGroup_iff'.mp W.2
  have hM : M = representation W * M * (representation W)ᴴ := by
    rw [← hc, Matrix.mul_assoc, g58d_rep_unitary', Matrix.mul_one]
  set T : Op (ABC d) := Matrix.kronecker (Matrix.kronecker (1 : Op (Fin d)) 1) (W : Op (Fin d)) with hT
  set Q : Op (ABC d) := Matrix.kronecker (Matrix.kronecker ((W : Op (Fin d)).map conj)
    ((W : Op (Fin d)).map conj)) (1 : Op (Fin d)) with hQ
  have hTQ : Tᴴ * representation W = Q := by
    rw [hT, hQ, representation]
    simp only [Matrix.kronecker]
    simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
      Matrix.one_mul, h1]
  have e1 : ∑ c, ∑ e, conj ((W : Op (Fin d)) c k) * M (y, c) (x, e) * (W : Op (Fin d)) e k =
      (Tᴴ * M * T) (y, k) (x, k) := by
    simp only [hT, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, RCLike.star_def]
    simp only [map_mul, apply_ite (starRingEnd ℂ), map_one, map_zero, Finset.sum_mul, ite_mul, mul_ite,
      one_mul, mul_one, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_ite_irrel, Finset.sum_const_zero]
    exact Finset.sum_comm
  have e2 : Tᴴ * M * T = Q * M * Qᴴ := by
    conv_lhs => rw [hM]
    rw [← hTQ, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  rw [e1, e2]
  simp only [hQ, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, RCLike.star_def, Matrix.map_apply]
  simp only [map_mul, apply_ite (starRingEnd ℂ), map_one, map_zero, Finset.sum_mul, ite_mul, mul_ite,
      one_mul, mul_one, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Complex.conj_conj]
  simp only [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv
    { toFun := fun p : Fin d × Fin d × Fin d × Fin d => (p.2.2.1, p.2.2.2, p.1, p.2.1)
      invFun := fun p : Fin d × Fin d × Fin d × Fin d => (p.2.2.1, p.2.2.2, p.1, p.2.1)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  intro p; rfl

theorem solution (d : ℕ) (hd : 2 ≤ d) (timing : Timing)
    (R : ReplicationChoiArray d) (hR : IsReplicationStrategy timing R) (hDiag : dephaseClassicalOutput R = R)
    (hCov : BlocksCommuteWithRotations (diagonalBlocks R)) (hRel : RelabelInvariant (diagonalBlocks R)) :
    ∀ U : (Matrix.unitaryGroup (Fin d) ℂ), ∀ sigma : Equiv.Perm (Fin d), ∀ i j,
      let V := pairAction ((U : Op (Fin d)) * permutationMatrix sigma)
      replica R U (sigma i) (sigma j) = V * replica R 1 i j * V.conjTranspose := by
  intro U σ i j V
  let W : (Matrix.unitaryGroup (Fin d) ℂ) := ⟨(U : Op (Fin d)) * permutationMatrix σ,
    Submonoid.mul_mem _ U.2 (g58d_perm_mem σ)⟩
  have hW : ∀ e k, (W : Op (Fin d)) e k = (U : Op (Fin d)) e (σ k) := by
    intro e k
    simp [W, Matrix.mul_apply, permutationMatrix]
  have hV : V = pairAction (W : Op (Fin d)) := rfl
  ext x y
  have step : replica R U (σ i) (σ j) x y = ∑ k, ∑ c, ∑ e,
      conj ((W : Op (Fin d)) c k) * diagonalBlocks R i j k (y, c) (x, e) * (W : Op (Fin d)) e k := by
    unfold replica
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hRel σ i j k]
    simp only [hW]
    rfl
  rw [step]
  rw [Finset.sum_congr rfl (fun k _ => g58d_slice W _ (hCov W i j k) k x y)]
  rw [hV]
  simp only [pairAction, replica, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, RCLike.star_def, OneMemClass.coe_one, Matrix.one_apply]
  simp only [map_mul, apply_ite (starRingEnd ℂ), map_one, map_zero, Finset.sum_mul, ite_mul, mul_ite,
      one_mul, mul_one, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Complex.conj_conj, Finset.mul_sum]
  simp only [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv
    { toFun := fun p : Fin d × Fin d × Fin d × Fin d × Fin d => (p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2, p.1)
      invFun := fun q : Fin d × Fin d × Fin d × Fin d × Fin d => (q.2.2.2.2, q.1, q.2.1, q.2.2.1, q.2.2.2.1)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  intro p
  simp only [Equiv.coe_fn_mk, diagonalBlocks]; ring
