-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P17.extremal_block_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T11:03:07.514808+00:00
-- url     : https://prove2.me/submissions/2d0b37d8-ef64-4c6e-9060-7f280b7da25d

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

theorem g58d_kernel (A : Matrix (Fin 2) (Fin 3) ℝ) : ∃ t : Fin 3 → ℝ, t ≠ 0 ∧ A.mulVec t = 0 := by
  have h := LinearMap.ker_ne_bot_of_finrank_lt (f := Matrix.mulVecLin A) (by simp)
  obtain ⟨t, ht, ht0⟩ := (Submodule.ne_bot_iff _).mp h
  exact ⟨t, ht0, ht⟩

theorem g58d_scale_mem (d : ℕ) (b : BlockArray) (hb : b ∈ cloningBlockSet d) (μ : Fin 5 × Fin 3 → ℝ)
    (hμ : ∀ p, 0 ≤ μ p)
    (hsum : ∀ s : Fin 2, (∑ l : Fin 5, ∑ v : Fin 3, (replicationSectorDimension d v : ℂ) *
      (((μ (l, v) : ℝ) : ℂ) * b l v s s)) = (pairDimension d s : ℂ)) :
    (fun l v => ((μ (l, v) : ℝ) : ℂ) • b l v) ∈ cloningBlockSet d := by
  obtain ⟨⟨hpsd, h1, h2, h3⟩, _⟩ := hb
  refine ⟨⟨fun l v => (hpsd l v).smul (Complex.zero_le_real.mpr (hμ _)), fun l => ?_, fun l => ?_,
    fun hd => ⟨fun l => ?_, fun v => ?_⟩⟩, fun s => ?_⟩
  · calc ((μ (l, 1) : ℝ) : ℂ) • b l 1 = ((μ (l, 1) : ℝ) : ℂ) • ((b l 1 0 0) • coordinateProjector 0) :=
          congrArg _ (h1 l)
      _ = (((μ (l, 1) : ℝ) : ℂ) * b l 1 0 0) • coordinateProjector 0 := smul_smul _ _ _
      _ = _ := by simp [Matrix.smul_apply]
  · calc ((μ (l, 2) : ℝ) : ℂ) • b l 2 = ((μ (l, 2) : ℝ) : ℂ) • ((b l 2 1 1) • coordinateProjector 1) :=
          congrArg _ (h2 l)
      _ = (((μ (l, 2) : ℝ) : ℂ) * b l 2 1 1) • coordinateProjector 1 := smul_smul _ _ _
      _ = _ := by simp [Matrix.smul_apply]
  · simp [(h3 hd).1 l]
  · simp [(h3 hd).2 v]
  · rw [← hsum s]
    simp [Matrix.smul_apply]

theorem solution (d : ℕ) (hd : 2 ≤ d) (b : BlockArray)
    (hb : b ∈ (cloningBlockSet d).extremePoints ℝ) :
    (blockSupport b).card ≤ 2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨p1, p2, p3, hp1, hp2, hp3, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp hcon
  simp only [blockSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2 hp3
  rw [mem_extremePoints] at hb
  obtain ⟨hmem, hext⟩ := hb
  have hpsd := hmem.1.1
  let ps : Fin 3 → Fin 5 × Fin 3 := ![p1, p2, p3]
  let c : Fin 2 → Fin 3 → ℂ := fun s i => (replicationSectorDimension d (ps i).2 : ℂ) * b (ps i).1 (ps i).2 s s
  have hcre : ∀ s i, c s i = (((c s i).re : ℝ) : ℂ) := by
    intro s i
    have h0 := (hpsd (ps i).1 (ps i).2).diag_nonneg (i := s)
    have him : (b (ps i).1 (ps i).2 s s).im = 0 := (Complex.nonneg_iff.mp h0).2.symm
    apply Complex.ext <;> simp [c, him]
  obtain ⟨t, ht0, htk⟩ := g58d_kernel (fun s i => (c s i).re)
  let τ : Fin 5 × Fin 3 → ℝ := fun p =>
    (if p = p1 then t 0 else 0) + (if p = p2 then t 1 else 0) + (if p = p3 then t 2 else 0)
  have hτsum : ∀ s : Fin 2, (∑ l : Fin 5, ∑ v : Fin 3, (replicationSectorDimension d v : ℂ) *
      (((τ (l, v) : ℝ) : ℂ) * b l v s s)) = 0 := by
    intro s
    have hk := congrFun htk s
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.zero_apply] at hk
    rw [← Fintype.sum_prod_type' (f := fun l v => (replicationSectorDimension d v : ℂ) *
      (((τ (l, v) : ℝ) : ℂ) * b l v s s))]
    simp only [τ, Complex.ofReal_add, add_mul, mul_add, Finset.sum_add_distrib, apply_ite (fun x : ℝ => (x : ℂ)),
      Complex.ofReal_zero, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have e : ∀ i, (replicationSectorDimension d (ps i).2 : ℂ) * (((t i : ℝ) : ℂ) * b (ps i).1 (ps i).2 s s) =
        (((c s i).re * t i : ℝ) : ℂ) := by
      intro i; rw [Complex.ofReal_mul, ← hcre]; simp only [c]; ring
    have e0 := e 0; have e1 := e 1; have e2 := e 2
    simp only [ps, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at e0 e1 e2
    rw [e0, e1, e2, ← Complex.ofReal_add, ← Complex.ofReal_add, hk, Complex.ofReal_zero]
  obtain ⟨i, hi⟩ : ∃ i, t i ≠ 0 := by
    by_contra hh; push_neg at hh; exact ht0 (funext hh)
  have hτi : τ (ps i) = t i := by
    fin_cases i <;> simp [τ, ps, h12, h13, h23, Ne.symm h12, Ne.symm h13, Ne.symm h23]
  have hbi : b (ps i).1 (ps i).2 ≠ 0 := by
    fin_cases i <;> simpa [ps] using (by assumption)
  set S := |t 0| + |t 1| + |t 2| with hS
  have hS0 : 0 ≤ S := by positivity
  set h : ℝ := 1 / (S + 1) with hh
  have hpos : 0 < h := by positivity
  have hhS : h * S < 1 := by rw [hh, div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]; linarith
  have hτb : ∀ p, |τ p| ≤ S := by
    intro p
    simp only [τ]
    have a0 := abs_nonneg (t 0); have a1 := abs_nonneg (t 1); have a2 := abs_nonneg (t 2)
    rw [abs_le]
    constructor <;> split_ifs <;>
      linarith [neg_abs_le (t 0), neg_abs_le (t 1), neg_abs_le (t 2), le_abs_self (t 0), le_abs_self (t 1),
        le_abs_self (t 2)]
  have hnn : ∀ (σ : ℝ), σ = 1 ∨ σ = -1 → ∀ p, 0 ≤ 1 + σ * h * τ p := by
    intro σ hσ p
    have := abs_le.mp (hτb p)
    have hp1 : h * τ p ≤ h * S := mul_le_mul_of_nonneg_left this.2 hpos.le
    have hp2 : -(h * S) ≤ h * τ p := by nlinarith [this.1]
    rcases hσ with rfl | rfl <;> nlinarith
  have hmemσ : ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      (fun l v => (((1 + σ * h * τ (l, v)) : ℝ) : ℂ) • b l v) ∈ cloningBlockSet d := by
    intro σ hσ
    refine g58d_scale_mem d b hmem _ (hnn σ hσ) (fun s => ?_)
    rw [← hmem.2 s]
    have e : ∀ l v, (replicationSectorDimension d v : ℂ) * ((((1 + σ * h * τ (l, v)) : ℝ) : ℂ) * b l v s s) =
        (replicationSectorDimension d v : ℂ) * b l v s s + ((σ * h : ℝ) : ℂ) *
          ((replicationSectorDimension d v : ℂ) * (((τ (l, v) : ℝ) : ℂ) * b l v s s)) := by
      intro l v; push_cast; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hτsum s, mul_zero, add_zero]
  have hmid : b ∈ openSegment ℝ (fun l v => (((1 + 1 * h * τ (l, v)) : ℝ) : ℂ) • b l v)
      (fun l v => (((1 + (-1) * h * τ (l, v)) : ℝ) : ℂ) • b l v) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext l v; ext r c
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    simp only [Complex.real_smul]
    push_cast; ring
  have heq := (hext _ (hmemσ 1 (Or.inl rfl)) _ (hmemσ (-1) (Or.inr rfl)) hmid).1
  have := congrFun (congrFun heq (ps i).1) (ps i).2
  simp only [hτi] at this
  have h2 : (((h * t i : ℝ)) : ℂ) • b (ps i).1 (ps i).2 = 0 := by
    have e : (((1 + 1 * h * t i) : ℝ) : ℂ) • b (ps i).1 (ps i).2 =
        b (ps i).1 (ps i).2 + (((h * t i : ℝ)) : ℂ) • b (ps i).1 (ps i).2 := by
      rw [show (((1 + 1 * h * t i) : ℝ) : ℂ) = 1 + (((h * t i : ℝ)) : ℂ) by push_cast; ring, add_smul, one_smul]
    rw [e] at this
    exact (add_eq_left.mp this)
  rcases smul_eq_zero.mp h2 with h3 | h3
  · have : h * t i = 0 := by exact_mod_cast h3
    rcases mul_eq_zero.mp this with h4 | h4
    · exact hpos.ne' h4
    · exact hi h4
  · exact hbi h3
