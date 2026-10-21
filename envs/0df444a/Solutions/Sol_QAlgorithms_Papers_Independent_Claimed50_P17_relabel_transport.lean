-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P17.relabel_transport
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:32:30.08074+00:00
-- url     : https://prove2.me/submissions/fb6e8928-7082-48d7-b9a1-b650d90bc520

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

theorem g58d_relabel_entry {d : ℕ} (R : ReplicationChoiArray d) (hDiag : dephaseClassicalOutput R = R)
    (i j : Fin d) (x y : ABCD d) :
    relabel R i j x y = ((Fintype.card (Equiv.Perm (Fin d)) : ℂ)⁻¹) *
      ∑ σ : Equiv.Perm (Fin d), R (σ i) (σ j) (x.1, σ x.2) (y.1, σ y.2) := by
  have hz : ∀ a b (p q : ABCD d), p.2 ≠ q.2 → R a b p q = 0 := fun a b p q h => by
    rw [← hDiag]; simp [dephaseClassicalOutput,
      QAlgorithms.Papers.Independent.Information100.P34.dephaseOutput, h]
  simp only [relabel, liftDiagonal, relabelBlocks, diagonalBlocks, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul]
  split_ifs with h
  · obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
    simp only at h; subst h; rfl
  · rw [Finset.sum_eq_zero (fun σ _ => hz _ _ _ _ (by simpa using h)), mul_zero]

theorem g58d_card_ne {d : ℕ} : ((Fintype.card (Equiv.Perm (Fin d)) : ℂ)) ≠ 0 := by
  exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin d))).ne'

theorem g58d_relabel_sum {d : ℕ} (R : ReplicationChoiArray d) (hDiag : dephaseClassicalOutput R = R)
    (M : Op (ABCD d)) (hM : ∀ σ : Equiv.Perm (Fin d), ∀ x y : ABCD d, M (x.1, σ x.2) (y.1, σ y.2) = M x y)
    (hs : (∑ i, ∑ j, R i j) = M) : (∑ i, ∑ j, relabel R i j) = M := by
  ext x y
  have hs' : ∀ σ : Equiv.Perm (Fin d), ∑ i, ∑ j, R (σ i) (σ j) (x.1, σ x.2) (y.1, σ y.2) = M x y := by
    intro σ
    rw [← hM σ x y, ← hs]
    simp only [Matrix.sum_apply]
    rw [Equiv.sum_comp σ (fun i => ∑ j, R i (σ j) (x.1, σ x.2) (y.1, σ y.2))]
    exact Finset.sum_congr rfl (fun i _ => Equiv.sum_comp σ (fun j => R i j (x.1, σ x.2) (y.1, σ y.2)))
  simp only [Matrix.sum_apply, g58d_relabel_entry R hDiag]
  calc _ = ((Fintype.card (Equiv.Perm (Fin d)) : ℂ)⁻¹) * ∑ i, ∑ j, ∑ σ : Equiv.Perm (Fin d),
        R (σ i) (σ j) (x.1, σ x.2) (y.1, σ y.2) := by simp only [Finset.mul_sum]
    _ = ((Fintype.card (Equiv.Perm (Fin d)) : ℂ)⁻¹) * ∑ σ : Equiv.Perm (Fin d), ∑ i, ∑ j,
        R (σ i) (σ j) (x.1, σ x.2) (y.1, σ y.2) := by
          congr 1
          exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm
    _ = ((Fintype.card (Equiv.Perm (Fin d)) : ℂ)⁻¹) * ∑ σ : Equiv.Perm (Fin d), M x y := by
          rw [Finset.sum_congr rfl (fun σ _ => hs' σ)]
    _ = M x y := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ g58d_card_ne,
            one_mul]

theorem solution (d : ℕ) (hd : 2 ≤ d) (timing : Timing) (R : ReplicationChoiArray d)
    (hR : IsReplicationStrategy timing R) (hDiag : dephaseClassicalOutput R = R)
    (hCov : BlocksCommuteWithRotations (diagonalBlocks R)) :
    IsReplicationStrategy timing (relabel R) ∧ BlocksCommuteWithRotations (diagonalBlocks (relabel R)) ∧
    RelabelInvariant (diagonalBlocks (relabel R)) ∧
    dephaseClassicalOutput (relabel R) = relabel R ∧ haarReplicationScore (relabel R) = haarReplicationScore R := by
  have hdb : diagonalBlocks (relabel R) = relabelBlocks (diagonalBlocks R) := by
    funext i j k; ext x y; simp [diagonalBlocks, relabel, liftDiagonal]
  have hcov2 : BlocksCommuteWithRotations (diagonalBlocks (relabel R)) := by
    intro U i j k
    rw [hdb]
    simp only [relabelBlocks, Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul, Finset.mul_sum, hCov U]
  have hpsd : ∀ i j, (relabel R i j).PosSemidef := by
    intro i j
    have : relabel R i j = ((Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹ : ℂ) •
        ∑ σ : Equiv.Perm (Fin d), (R (σ i) (σ j)).submatrix (fun p : ABCD d => (p.1, σ p.2))
          (fun p : ABCD d => (p.1, σ p.2)) := by
      ext x y
      rw [g58d_relabel_entry R hDiag]
      simp [Matrix.sum_apply]
    rw [this]
    refine Matrix.PosSemidef.smul ?_ ?_
    · exact Matrix.posSemidef_sum _ (fun σ _ => (hR.1 _ _).submatrix _)
    · rw [← Complex.ofReal_inv]; exact Complex.zero_le_real.mpr (inv_nonneg.mpr (Nat.cast_nonneg _))
  refine ⟨⟨hpsd, ?_⟩, hcov2, ?_, ?_, ?_⟩
  · cases timing with
    | cloning =>
      obtain ⟨S, hS, hS1, hS2⟩ := hR.2
      refine ⟨S, hS, hS1, g58d_relabel_sum R hDiag _ ?_ hS2⟩
      intro σ x y
      simp [cloningTotal, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
    | learning =>
      obtain ⟨S, hS, hS1, hS2⟩ := hR.2
      refine ⟨S, hS, hS1, g58d_relabel_sum R hDiag _ ?_ hS2⟩
      intro σ x y
      simp [learningTotal]
  · intro τ i j k
    rw [hdb]
    simp only [relabelBlocks]
    congr 1
    exact (Equiv.sum_comp (Equiv.mulRight τ) (fun σ => diagonalBlocks R (σ i) (σ j) (σ k))).symm
  · funext i j; ext x y
    simp only [dephaseClassicalOutput, QAlgorithms.Papers.Independent.Information100.P34.dephaseOutput,
      relabel, liftDiagonal]
    split_ifs <;> simp_all
  · rw [g58d_score_cov _ hcov2, g58d_score_cov _ hCov, hdb]
    congr 1
    simp only [← Complex.re_sum]
    congr 1
    simp only [relabelBlocks, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, ← Finset.mul_sum]
    set g : Fin d → Fin d → Fin d → ℂ := fun i j k => diagonalBlocks R i j k ((i, j), k) ((i, j), k)
    have hg : ∀ σ : Equiv.Perm (Fin d), ∀ i j k,
        diagonalBlocks R (σ i) (σ j) (σ k) ((i, j), k) ((i, j), k) = g (σ i) (σ j) (σ k) := by
      intro σ i j k
      exact (g58d_perm_cov _ σ (hCov _ _ _ _) ((i, j), k) ((i, j), k)).symm
    simp only [hg]
    have hsw : ∀ σ : Equiv.Perm (Fin d), ∑ i, ∑ j, ∑ k, g (σ i) (σ j) (σ k) = ∑ i, ∑ j, ∑ k, g i j k := by
      intro σ
      rw [Equiv.sum_comp σ (fun i => ∑ j, ∑ k, g i (σ j) (σ k))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Equiv.sum_comp σ (fun j => ∑ k, g i j (σ k))]
      exact Finset.sum_congr rfl (fun j _ => Equiv.sum_comp σ (fun k => g i j k))
    calc _ = ((Fintype.card (Equiv.Perm (Fin d)) : ℂ)⁻¹) * ∑ σ : Equiv.Perm (Fin d), ∑ i, ∑ j, ∑ k,
          g (σ i) (σ j) (σ k) := by
          congr 1
          exact (Finset.sum_congr rfl fun i _ =>
            (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans Finset.sum_comm).trans Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_congr rfl (fun σ _ => hsw σ), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ← mul_assoc, inv_mul_cancel₀ g58d_card_ne, one_mul]
