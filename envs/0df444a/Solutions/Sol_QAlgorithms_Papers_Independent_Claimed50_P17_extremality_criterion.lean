-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P17.extremality_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T11:13:42.203014+00:00
-- url     : https://prove2.me/submissions/81ff78bc-3f93-40b4-b15e-489c2f2d4f95

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

theorem g58d_convex (d : ℕ) : Convex ℝ (cloningBlockSet d) := by
  intro x hx y hy p q hp hq hpq
  have hxe : ∀ l v, (p • x + q • y) l v = ((p : ℝ) : ℂ) • x l v + ((q : ℝ) : ℂ) • y l v := by
    intro l v; ext r c; simp [Complex.real_smul]
  obtain ⟨⟨hxp, hx1, hx2, hx3⟩, hxs⟩ := hx
  obtain ⟨⟨hyp, hy1, hy2, hy3⟩, hys⟩ := hy
  refine ⟨⟨fun l v => ?_, fun l => ?_, fun l => ?_, fun hd => ⟨fun l => ?_, fun v => ?_⟩⟩, fun s => ?_⟩
  · rw [hxe]
    exact ((hxp l v).smul (Complex.zero_le_real.mpr hp)).add ((hyp l v).smul (Complex.zero_le_real.mpr hq))
  · rw [hxe]
    conv_lhs => rw [hx1 l, hy1 l]
    ext r c; simp [Matrix.smul_apply, coordinateProjector]
    split_ifs <;> ring
  · rw [hxe]
    conv_lhs => rw [hx2 l, hy2 l]
    ext r c; simp [Matrix.smul_apply, coordinateProjector]
    split_ifs <;> ring
  · rw [hxe, (hx3 hd).1 l, (hy3 hd).1 l]; simp
  · rw [hxe, (hx3 hd).2 v, (hy3 hd).2 v]; simp
  · simp only [hxe, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    have e1 : ∀ (z : BlockArray) (r : ℝ), (∑ l : Fin 5, ∑ v : Fin 3, (replicationSectorDimension d v : ℂ) *
        ((r : ℂ) * z l v s s)) = (r : ℂ) * ∑ l : Fin 5, ∑ v : Fin 3,
          (replicationSectorDimension d v : ℂ) * z l v s s := by
      intro z r; simp only [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ =>
        Finset.sum_congr rfl (fun _ _ => by ring))
    rw [e1 x p, e1 y q, hxs s, hys s, ← add_mul, ← Complex.ofReal_add, hpq]; simp

theorem solution (d : ℕ) (hd : 2 ≤ d) (b : BlockArray)
    (hb : b ∈ cloningBlockSet d) :
    b ∈ (cloningBlockSet d).extremePoints ℝ ↔
      ∀ z : BlockArray, IsPerturbation d b z → z = 0 := by
  constructor
  · intro hext z hz
    rw [mem_extremePoints] at hext
    obtain ⟨_, ε, hε, hzε⟩ := hz
    have h1 := hzε ε ⟨by linarith, le_refl _⟩
    have h2 := hzε (-ε) ⟨le_refl _, by linarith⟩
    have hmid : b ∈ openSegment ℝ (b + ε • z) (b + (-ε) • z) := by
      refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      rw [neg_smul, ← sub_eq_add_neg, smul_add, smul_sub, ← add_add_sub_cancel]
      module
    have := (hext.2 _ h1 _ h2 hmid).1
    have h3 : ε • z = 0 := by simpa using this
    exact (smul_eq_zero.mp h3).resolve_left hε.ne'
  · intro hpert
    rw [mem_extremePoints]
    refine ⟨hb, fun x1 hx1 x2 hx2 hseg => ?_⟩
    obtain ⟨a, c, ha, hc, hac, hbx⟩ := hseg
    have hrel : c • (x2 - b) = -(a • (x1 - b)) := by
      rw [← hbx]
      have : c = 1 - a := by linarith
      subst this
      module
    have hz : x1 - b = 0 := by
      apply hpert
      refine ⟨fun l v => ?_, min 1 (a / c), lt_min one_pos (div_pos ha hc), fun h hh => ?_⟩
      · exact ((hx1.1.1 l v).1).sub ((hb.1.1 l v).1)
      · obtain ⟨hh1, hh2⟩ := hh
        rcases le_total 0 h with h0 | h0
        · exact (g58d_convex d).add_smul_sub_mem hb hx1 ⟨h0, le_trans hh2 (min_le_left _ _)⟩
        · have hle : -h ≤ a / c := by
            have := le_trans (neg_le.mp hh1) (min_le_right _ _)
            linarith
          have hs1 : 0 ≤ -h * c / a := by
            apply div_nonneg _ ha.le; nlinarith
          have hs2 : -h * c / a ≤ 1 := by
            rw [div_le_one ha]
            have := (le_div_iff₀ hc).mp hle
            linarith
          have key : b + h • (x1 - b) = b + (-h * c / a) • (x2 - b) := by
            congr 1
            have : (-h * c / a) • (x2 - b) = (-h / a) • (c • (x2 - b)) := by
              rw [smul_smul]; congr 1; field_simp
            rw [this, hrel, smul_neg, smul_smul, ← neg_smul]
            congr 1; field_simp
          rw [key]
          exact (g58d_convex d).add_smul_sub_mem hb hx2 ⟨hs1, hs2⟩
    have e1 : x1 = b := sub_eq_zero.mp hz
    refine ⟨e1, ?_⟩
    rw [e1, sub_self, smul_zero, neg_zero] at hrel
    exact sub_eq_zero.mp ((smul_eq_zero.mp hrel).resolve_left hc.ne')
