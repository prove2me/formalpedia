-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P17.exchange_transport
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:36:32.464589+00:00
-- url     : https://prove2.me/submissions/1b1bf6c3-d8bd-434d-b8e4-4c22a319ee19

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

def g58d_swE (d : ℕ) : ABC d ≃ ABC d :=
  { toFun := fun a => ((a.1.2, a.1.1), a.2), invFun := fun a => ((a.1.2, a.1.1), a.2),
    left_inv := fun _ => rfl, right_inv := fun _ => rfl }

theorem g58d_half_nonneg : (0 : ℂ) ≤ (1/2 : ℂ) := by
  rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring]
  exact Complex.zero_le_real.mpr (by norm_num)

theorem g58d_exch_trace {d : ℕ} (R : ReplicationChoiArray d) (U : (Matrix.unitaryGroup (Fin d) ℂ)) (i j : Fin d) :
    Matrix.trace (replica (exchange R) U i j *
      Matrix.kronecker (measurementEffect U i) (measurementEffect U j)) =
    Matrix.trace (replica R U j i *
      Matrix.kronecker (measurementEffect U j) (measurementEffect U i)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, replica, exchange, Matrix.kronecker,
    Matrix.kroneckerMap_apply, measurementEffect, Finset.sum_mul, Fintype.sum_prod_type]
  simp only [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv
    { toFun := fun p : Fin d × Fin d × Fin d × Fin d × Fin d × Fin d × Fin d =>
        (p.2.1, p.1, p.2.2.2.1, p.2.2.1, p.2.2.2.2)
      invFun := fun p : Fin d × Fin d × Fin d × Fin d × Fin d × Fin d × Fin d =>
        (p.2.1, p.1, p.2.2.2.1, p.2.2.1, p.2.2.2.2)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  intro x
  simp only [Equiv.coe_fn_mk]; ring

theorem g58d_symm_si {d : ℕ} (R : ReplicationChoiArray d) (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    scoreIntegrand (symmetrize R) U = scoreIntegrand R U := by
  have hlin : ∀ i j, replica (symmetrize R) U i j =
      (1/2 : ℂ) • (replica R U i j + replica (exchange R) U i j) := by
    intro i j; ext x y
    simp only [replica, symmetrize, Pi.smul_apply, Pi.add_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl
      (fun _ _ => by ring)))
  have ht : ∀ i j, (Matrix.trace (replica (symmetrize R) U i j *
      Matrix.kronecker (measurementEffect U i) (measurementEffect U j))).re =
      (1/2 : ℝ) * ((Matrix.trace (replica R U i j *
      Matrix.kronecker (measurementEffect U i) (measurementEffect U j))).re +
      (Matrix.trace (replica R U j i *
      Matrix.kronecker (measurementEffect U j) (measurementEffect U i))).re) := by
    intro i j
    rw [hlin, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul, Matrix.trace_add, g58d_exch_trace,
      smul_eq_mul, show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul, Complex.add_re]
  unfold scoreIntegrand
  simp only [ht, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => (Matrix.trace (replica R U j i *
      Matrix.kronecker (measurementEffect U j) (measurementEffect U i))).re)]
  ring

theorem solution (d : ℕ) (hd : 2 ≤ d) (timing : Timing) (R : ReplicationChoiArray d)
    (hR : IsReplicationStrategy timing R) :
    IsReplicationStrategy timing (symmetrize R) ∧ exchange (symmetrize R) = symmetrize R ∧
    haarReplicationScore (symmetrize R) = haarReplicationScore R ∧
    (dephaseClassicalOutput R = R → dephaseClassicalOutput (symmetrize R) = symmetrize R) ∧
    (BlocksCommuteWithRotations (diagonalBlocks R) → BlocksCommuteWithRotations (diagonalBlocks (symmetrize R))) ∧
    (RelabelInvariant (diagonalBlocks R) → RelabelInvariant (diagonalBlocks (symmetrize R))) := by
  have hdb : ∀ i j k, diagonalBlocks (symmetrize R) i j k = (1/2 : ℂ) • (diagonalBlocks R i j k +
      (diagonalBlocks R j i k).submatrix (g58d_swE d) (g58d_swE d)) := by
    intro i j k; ext x y; rfl
  have hsum : ∀ x y : ABCD d, (∑ i, ∑ j, symmetrize R i j) x y =
      (1/2 : ℂ) * ((∑ i, ∑ j, R i j) x y + (∑ i, ∑ j, R i j) (g58d_swE d x.1, x.2) (g58d_swE d y.1, y.2)) := by
    intro x y
    simp only [Matrix.sum_apply, symmetrize, exchange, Pi.smul_apply, Pi.add_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      ← Finset.mul_sum, Finset.sum_add_distrib]
    congr 2
    exact Finset.sum_comm
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((hR.1 i j).add ((hR.1 j i).submatrix _)).smul g58d_half_nonneg
  · cases timing with
    | cloning =>
      obtain ⟨S, hS, hS1, hS2⟩ := hR.2
      refine ⟨(1/2 : ℂ) • (S + S.submatrix (g58d_swE d) (g58d_swE d)),
        (hS.add (hS.submatrix _)).smul g58d_half_nonneg, ?_, ?_⟩
      · ext a b
        have h1 := congrFun (congrFun hS1 a) b
        have h2 := congrFun (congrFun hS1 (a.2, a.1)) (b.2, b.1)
        simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.one_apply] at h1 h2 ⊢
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.submatrix_apply, smul_eq_mul,
          Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [h1]
        simp only [g58d_swE, Equiv.coe_fn_mk]
        rw [h2]
        obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
        by_cases h : (a1, a2) = (b1, b2)
        · rw [if_pos h, if_pos (by simp only [Prod.mk.injEq] at h ⊢; exact ⟨h.2, h.1⟩)]; norm_num
        · rw [if_neg h, if_neg (fun hh => h (by simp only [Prod.mk.injEq] at hh ⊢; exact ⟨hh.2, hh.1⟩))]
          norm_num
      · ext x y
        rw [hsum, hS2]
        simp [cloningTotal, Matrix.kronecker, Matrix.kroneckerMap_apply, g58d_swE]
        ring
    | learning =>
      obtain ⟨S, hS, hS1, hS2⟩ := hR.2
      refine ⟨S, hS, hS1, ?_⟩
      ext x y
      rw [hsum, hS2]
      have hl : learningTotal S (g58d_swE d x.1, x.2) (g58d_swE d y.1, y.2) = learningTotal S x y := by
        obtain ⟨⟨⟨a, b⟩, c⟩, e⟩ := x; obtain ⟨⟨⟨a', b'⟩, c'⟩, e'⟩ := y
        simp only [learningTotal, g58d_swE, Equiv.coe_fn_mk, Prod.mk.injEq]
        congr 1
        apply propext; tauto
      rw [hl]; ring
  · funext i j; ext x y
    simp only [exchange, symmetrize, Pi.smul_apply, Pi.add_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  · unfold haarReplicationScore
    simp only [g58d_symm_si]
  · intro hD
    have hz : ∀ a b (p q : ABCD d), p.2 ≠ q.2 → R a b p q = 0 := fun a b p q h => by
      rw [← hD]; simp [dephaseClassicalOutput,
        QAlgorithms.Papers.Independent.Information100.P34.dephaseOutput, h]
    funext i j; ext x y
    simp only [dephaseClassicalOutput, QAlgorithms.Papers.Independent.Information100.P34.dephaseOutput,
      symmetrize, exchange, Pi.smul_apply, Pi.add_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    split_ifs with h
    · rfl
    · rw [hz _ _ _ _ h, hz j i (((x.1.1.2, x.1.1.1), x.1.2), x.2) (((y.1.1.2, y.1.1.1), y.1.2), y.2) h]
      ring
  · intro hC U i j k
    have hrep : representation U = (representation U).submatrix (g58d_swE d) (g58d_swE d) := by
      ext a b
      simp only [representation, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.submatrix_apply,
        g58d_swE, Equiv.coe_fn_mk]
      ring
    have hsub : ∀ M : Op (ABC d), M.submatrix (g58d_swE d) (g58d_swE d) * representation U =
        (M * representation U).submatrix (g58d_swE d) (g58d_swE d) := by
      intro M; conv_lhs => rw [hrep]
      exact Matrix.submatrix_mul_equiv _ _ _ _ _
    have hsub2 : ∀ M : Op (ABC d), representation U * M.submatrix (g58d_swE d) (g58d_swE d) =
        (representation U * M).submatrix (g58d_swE d) (g58d_swE d) := by
      intro M; conv_lhs => rw [hrep]
      exact Matrix.submatrix_mul_equiv _ _ _ _ _
    rw [hdb, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, hsub, hsub2, hC U i j k,
      hC U j i k]
  · intro hRel σ i j k
    rw [hdb, hdb, hRel σ i j k, hRel σ j i k]
