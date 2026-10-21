-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P17.learning_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:57:55.903541+00:00
-- url     : https://prove2.me/submissions/7b5a661f-5d3b-46d1-8930-d6f5bde49bf6

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

theorem g58d_rep_unitary' {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    representation U * (representation U)ᴴ = 1 :=
  mul_eq_one_comm.mp (g58d_rep_unitary U)

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

theorem g58d_si_le {d : ℕ} (hd : 0 < d) (R : ReplicationChoiArray d) (hR : IsReplicationStrategy .cloning R)
    (U : (Matrix.unitaryGroup (Fin d) ℂ)) : scoreIntegrand R U ≤ 1 := by
  obtain ⟨S, hS, hS1, hS2⟩ := hR.2
  have hblock : ∀ k, (∑ i, ∑ j, diagonalBlocks R i j k) = S := by
    intro k; ext x y
    have := congrFun (congrFun hS2 (x, k)) (y, k)
    simp only [Matrix.sum_apply, cloningTotal, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.one_apply, if_true, mul_one] at this
    simpa [diagonalBlocks, Matrix.sum_apply] using this
  set A := representation U with hA
  let f : ABC d → Op (ABC d) → ℝ := fun v M => ((Aᴴ * M * A) v v).re
  have fnn : ∀ v M, M.PosSemidef → 0 ≤ f v M := by
    intro v M hM
    have := (hM.conjTranspose_mul_mul_same A).diag_nonneg (i := v)
    exact (Complex.nonneg_iff.mp this).1
  have fadd : ∀ v k, f v (∑ i, ∑ j, diagonalBlocks R i j k) = ∑ i, ∑ j, f v (diagonalBlocks R i j k) := by
    intro v k
    simp only [f, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, Complex.re_sum]
  have hpsdB : ∀ i j k, (diagonalBlocks R i j k).PosSemidef := fun i j k =>
    (hR.1 i j).submatrix (fun x : ABC d => (x, k))
  have hle : ∀ i j k, f ((i, j), k) (diagonalBlocks R i j k) ≤ f ((i, j), k) S := by
    intro i j k
    rw [← hblock k, fadd]
    calc f ((i, j), k) (diagonalBlocks R i j k) ≤ ∑ j', f ((i, j), k) (diagonalBlocks R i j' k) :=
          Finset.single_le_sum (f := fun j' => f ((i, j), k) (diagonalBlocks R i j' k))
            (fun j' _ => fnn _ _ (hpsdB _ _ _)) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', f ((i, j), k) (diagonalBlocks R i' j' k) :=
          Finset.single_le_sum (f := fun i' => ∑ j', f ((i, j), k) (diagonalBlocks R i' j' k))
            (fun i' _ => Finset.sum_nonneg (fun j' _ => fnn _ _ (hpsdB _ _ _))) (Finset.mem_univ i)
  have htr : ∑ i, ∑ j, ∑ k, f ((i, j), k) S = (d : ℝ)^2 := by
    have e1 : ∑ i, ∑ j, ∑ k, f ((i, j), k) S = (Matrix.trace (Aᴴ * S * A)).re := by
      simp only [Matrix.trace, Matrix.diag, Complex.re_sum, Fintype.sum_prod_type, f]
    rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hA, g58d_rep_unitary', Matrix.one_mul]
    have e2 : Matrix.trace S = Matrix.trace (QAlgorithms.traceRight S) := by
      simp [Matrix.trace, QAlgorithms.traceRight, Fintype.sum_prod_type]
    rw [e2, hS1]
    simp [Matrix.trace_one]; ring
  have hsi : scoreIntegrand R U = (1 / (d : ℝ)^2) * ∑ i, ∑ j, ∑ k, f ((i, j), k) (diagonalBlocks R i j k) := by
    unfold scoreIntegrand
    congr 1
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [g58d_term, Complex.re_sum]
  rw [hsi]
  have hd' : (0 : ℝ) < (d : ℝ)^2 := by positivity
  calc (1 / (d : ℝ)^2) * ∑ i, ∑ j, ∑ k, f ((i, j), k) (diagonalBlocks R i j k)
      ≤ (1 / (d : ℝ)^2) * ∑ i, ∑ j, ∑ k, f ((i, j), k) S := by
        gcongr with i _ j _ k _
        exact hle i j k
    _ = 1 := by rw [htr]; field_simp

theorem g58d_score_le {d : ℕ} (hd : 0 < d) (R : ReplicationChoiArray d) (hR : IsReplicationStrategy .cloning R) :
    haarReplicationScore R ≤ 1 := by
  unfold haarReplicationScore
  by_cases hI : Integrable (scoreIntegrand R) (QAlgorithms.Schur.unitaryHaar d)
  · have hu : QAlgorithms.Schur.unitaryHaar d Set.univ = 1 := Measure.haarMeasure_self
    haveI : IsFiniteMeasure (QAlgorithms.Schur.unitaryHaar d) := ⟨by rw [hu]; exact ENNReal.one_lt_top⟩
    calc ∫ U, scoreIntegrand R U ∂QAlgorithms.Schur.unitaryHaar d
        ≤ ∫ U, (1 : ℝ) ∂QAlgorithms.Schur.unitaryHaar d :=
          integral_mono hI (integrable_const 1) (fun U => g58d_si_le hd R hR U)
      _ = 1 := by simp [Measure.real, hu]
  · rw [integral_undef hI]; norm_num

theorem g58d_learn_to_clone {d : ℕ} (rho : Op (Fin d)) :
    learningTotal rho = cloningTotal (Matrix.kronecker (1 : Op (AB d)) rho) := by
  ext x y
  simp only [learningTotal, cloningTotal, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
  split_ifs <;> simp_all

theorem solution (d : ℕ) (hd : 2 ≤ d) (R : ReplicationChoiArray d)
    (hR : IsReplicationStrategy .learning R) :
    IsReplicationStrategy .cloning (learningToCloning R) ∧
    (∀ U : (Matrix.unitaryGroup (Fin d) ℂ), ∀ i j, replica (learningToCloning R) U i j = replica R U i j) ∧
    haarReplicationScore (learningToCloning R) = haarReplicationScore R ∧
    sSup (scoreValues d .learning) ≤ sSup (scoreValues d .cloning) := by
  have incl : ∀ R : ReplicationChoiArray d, IsReplicationStrategy .learning R →
      IsReplicationStrategy .cloning (learningToCloning R) := by
    intro R hR
    obtain ⟨rho, hr, hr1, hr2⟩ := hR.2
    refine ⟨hR.1, Matrix.kronecker (1 : Op (AB d)) rho, Matrix.PosSemidef.one.kronecker hr, ?_, ?_⟩
    · ext a b
      simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
      show ∑ h, (1 : Op (AB d)) a b * rho h h = _
      rw [← Finset.mul_sum]
      have : ∑ x, rho x x = 1 := hr1
      rw [this, mul_one]
    · rw [← g58d_learn_to_clone]; exact hr2
  refine ⟨incl R hR, fun U i j => rfl, rfl, ?_⟩
  have hd0 : 0 < d := by omega
  apply csSup_le_csSup
  · refine ⟨1, ?_⟩
    rintro v ⟨R', hR', rfl⟩
    exact g58d_score_le hd0 R' hR'
  · let i0 : Fin d := ⟨0, hd0⟩
    let rho : Op (Fin d) := Matrix.diagonal (fun a => if a = i0 then 1 else 0)
    have hrho : rho.PosSemidef := Matrix.PosSemidef.diagonal (fun a => by
      simp only [Pi.zero_apply]; split_ifs <;> simp)
    refine ⟨_, fun i j => if i = i0 ∧ j = i0 then learningTotal rho else 0, ⟨fun i j => ?_, rho, hrho, ?_, ?_⟩, rfl⟩
    · show Matrix.PosSemidef (if i = i0 ∧ j = i0 then learningTotal rho else 0)
      split_ifs
      · rw [g58d_learn_to_clone]; exact (Matrix.PosSemidef.one.kronecker hrho).kronecker Matrix.PosSemidef.one
      · exact Matrix.PosSemidef.zero
    · simp [rho, Matrix.trace_diagonal]
    · simp [ite_and, Finset.sum_ite_eq']
  · rintro v ⟨R', hR', rfl⟩
    exact ⟨learningToCloning R', incl R' hR', rfl⟩
