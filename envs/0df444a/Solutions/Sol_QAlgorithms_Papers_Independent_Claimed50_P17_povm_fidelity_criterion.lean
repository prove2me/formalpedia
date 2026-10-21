-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P17.povm_fidelity_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T11:16:32.029319+00:00
-- url     : https://prove2.me/submissions/caaa7ab5-990a-4f51-98f5-d9f272fca888

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

open QAlgorithms

theorem g58d_tr_eff {d : ℕ} (U : (Matrix.unitaryGroup (Fin d) ℂ)) (i : Fin d) (M : Op (Fin d)) :
    Matrix.trace (measurementEffect U i * M) =
      star (fun a => (U : Op (Fin d)) a i) ⬝ᵥ (M *ᵥ (fun a => (U : Op (Fin d)) a i)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, measurementEffect, dotProduct, Matrix.mulVec,
    Pi.star_apply, RCLike.star_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem g58d_core {d : ℕ} (hd : 0 < d) (U : (Matrix.unitaryGroup (Fin d) ℂ)) (Q : Fin d → Op (Fin d))
    (hQ : IsPOVM Q) :
    povmFidelity (measurementEffect U) Q ≤ 1 ∧
    (povmFidelity (measurementEffect U) Q = 1 → ∀ i, measurementEffect U i = Q i) := by
  set u : Fin d → Fin d → ℂ := fun i a => (U : Op (Fin d)) a i with hu
  have hUU : (U : Op (Fin d))ᴴ * (U : Op (Fin d)) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have hUU' : (U : Op (Fin d)) * (U : Op (Fin d))ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  have horth : ∀ i j, star (u i) ⬝ᵥ u j = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hUU i) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at this
    simpa [dotProduct, u] using this
  set q : Fin d → Fin d → ℂ := fun j i => star (u i) ⬝ᵥ (Q j *ᵥ u i) with hq
  have hqnn : ∀ j i, 0 ≤ q j i := fun j i =>
    (Matrix.posSemidef_iff_dotProduct_mulVec.mp (hQ.1 j)).2 (u i)
  have hqsum : ∀ i, ∑ j, q j i = 1 := by
    intro i
    simp only [hq, ← dotProduct_sum, ← Matrix.sum_mulVec, hQ.2, Matrix.one_mulVec, horth, if_true]
  have hqre : ∀ j i, ((q j i).re : ℂ) = q j i := fun j i =>
    Complex.ext (by simp) (by simp [(Complex.nonneg_iff.mp (hqnn j i)).2])
  have hqsumre : ∀ i, ∑ j, (q j i).re = 1 := by
    intro i; have := congrArg Complex.re (hqsum i); simpa [Complex.re_sum] using this
  have hqle : ∀ i, (q i i).re ≤ 1 := by
    intro i; rw [← hqsumre i]
    exact Finset.single_le_sum (f := fun j => (q j i).re)
      (fun j _ => (Complex.nonneg_iff.mp (hqnn j i)).1) (Finset.mem_univ i)
  have hF : povmFidelity (measurementEffect U) Q = (1 / (d : ℝ)) * ∑ i, (q i i).re := by
    unfold povmFidelity; congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [g58d_tr_eff]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨?_, fun h1 => ?_⟩
  · rw [hF, div_mul_eq_mul_div, one_mul, div_le_one hdpos]
    calc ∑ i, (q i i).re ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hqle i)
      _ = d := by simp
  · -- every q i i = 1
    rw [hF] at h1
    have hsum : ∑ i, (1 - (q i i).re) = 0 := by
      rw [Finset.sum_sub_distrib]; simp
      field_simp at h1; linarith
    have hall : ∀ i, (q i i).re = 1 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.mpr (hqle i))).mp hsum i
        (Finset.mem_univ i)
      linarith
    have hoff : ∀ j i, j ≠ i → q j i = 0 := by
      intro j i hji
      have h2 := hqsumre i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hall i] at h2
      have h3 : ∑ k ∈ Finset.univ.erase i, (q k i).re = 0 := by linarith
      have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => (Complex.nonneg_iff.mp (hqnn k i)).1)).mp h3 j
        (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
      rw [← hqre, h4]; simp
    have hker : ∀ j i, j ≠ i → Q j *ᵥ u i = 0 := fun j i hji =>
      ((hQ.1 j).dotProduct_mulVec_zero_iff (u i)).mp (hoff j i hji)
    have hfix : ∀ j, Q j *ᵥ u j = u j := by
      intro j
      have : (∑ k, Q k) *ᵥ u j = u j := by rw [hQ.2, Matrix.one_mulVec]
      rw [Matrix.sum_mulVec, Finset.sum_eq_single j (fun k _ hk => hker k j hk) (by simp)] at this
      exact this
    intro j
    ext a b
    have hQ' : Q j = Q j * ((U : Op (Fin d)) * (U : Op (Fin d))ᴴ) := by rw [hUU', Matrix.mul_one]
    rw [hQ', ← Matrix.mul_assoc]
    have hcol : ∀ i, (Q j * (U : Op (Fin d))) a i = (Q j *ᵥ u i) a := by
      intro i; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, u]
    simp only [Matrix.mul_apply (M := Q j * (U : Op (Fin d))), hcol, Matrix.conjTranspose_apply,
      RCLike.star_def]
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [hker j i (Ne.symm hi)]; simp) (by simp), hfix j]
    simp [measurementEffect, u]

theorem solution (d : ℕ) (hd : 0 < d)
    (P Q : Fin d → Op (Fin d)) (hP : IsPOVM P) (hQ : IsPOVM Q)
    (hBasis : IsRankOnePVM P ∨ IsRankOnePVM Q) :
    (povmFidelity P Q = 1 ↔ ∀ i, P i = Q i) ∧ povmFidelity P Q ≤ 1 := by
  have hsymm : ∀ P Q : Fin d → Op (Fin d), povmFidelity P Q = povmFidelity Q P := by
    intro P Q; unfold povmFidelity; congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [Matrix.trace_mul_comm])
  have hself : ∀ U : (Matrix.unitaryGroup (Fin d) ℂ),
      povmFidelity (measurementEffect U) (measurementEffect U) = 1 := by
    intro U
    have hUU : (U : Op (Fin d))ᴴ * (U : Op (Fin d)) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
    have hn : ∀ i, ∑ a, (U : Op (Fin d)) a i * conj ((U : Op (Fin d)) a i) = 1 := by
      intro i
      have := congrFun (congrFun hUU i) i
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, if_true,
        RCLike.star_def] at this
      rw [← this]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    unfold povmFidelity
    have : ∀ i, (Matrix.trace (measurementEffect U i * measurementEffect U i)).re = 1 := by
      intro i
      have e : Matrix.trace (measurementEffect U i * measurementEffect U i) =
          (∑ a, (U : Op (Fin d)) a i * conj ((U : Op (Fin d)) a i)) *
          (∑ a, (U : Op (Fin d)) a i * conj ((U : Op (Fin d)) a i)) := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, measurementEffect, Finset.sum_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
      rw [e, hn]; simp
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  rcases hBasis with ⟨U, rfl⟩ | ⟨U, rfl⟩
  · obtain ⟨h1, h2⟩ := g58d_core hd U Q hQ
    refine ⟨⟨h2, fun h => ?_⟩, h1⟩
    rw [show Q = measurementEffect U from (funext h).symm]; exact hself U
  · obtain ⟨h1, h2⟩ := g58d_core hd U P hP
    rw [hsymm]
    refine ⟨⟨fun h i => (h2 h i).symm, fun h => ?_⟩, h1⟩
    rw [show P = measurementEffect U from funext h]; exact hself U
