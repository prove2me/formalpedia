-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P17.extremal_block_ranks
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T11:11:28.314721+00:00
-- url     : https://prove2.me/submissions/2688d1d8-2704-424d-a86a-5f10c2d24b64

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

theorem g58d_real2 (a c gr gi x0r x0i x1r x1i : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hd : gr * gr + gi * gi ≤ a * c) :
    0 ≤ a * (x0r^2 + x0i^2) + c * (x1r^2 + x1i^2) + 2 * gr * (x0r * x1r + x0i * x1i) +
      2 * gi * (x0i * x1r - x0r * x1i) := by
  have key : a * (a * (x0r^2 + x0i^2) + c * (x1r^2 + x1i^2) + 2 * gr * (x0r * x1r + x0i * x1i) +
      2 * gi * (x0i * x1r - x0r * x1i)) =
      (a * x0r + gr * x1r - gi * x1i)^2 + (a * x0i + gr * x1i + gi * x1r)^2 +
      (a * c - gr * gr - gi * gi) * (x1r^2 + x1i^2) := by ring
  rcases ha.lt_or_eq with hpos | hzero
  · have h2 : 0 ≤ a * (a * (x0r^2 + x0i^2) + c * (x1r^2 + x1i^2) + 2 * gr * (x0r * x1r + x0i * x1i) +
        2 * gi * (x0i * x1r - x0r * x1i)) := by
      rw [key]; have : 0 ≤ a * c - gr * gr - gi * gi := by linarith
      positivity
    exact (mul_nonneg_iff_of_pos_left hpos).mp h2
  · subst hzero
    have hgr : gr = 0 := by nlinarith [mul_self_nonneg gr, mul_self_nonneg gi]
    have hgi : gi = 0 := by nlinarith [mul_self_nonneg gr, mul_self_nonneg gi]
    subst hgr; subst hgi
    have : 0 ≤ c * (x1r^2 + x1i^2) := by positivity
    linarith

theorem g58d_psd2 (M : Matrix (Fin 2) (Fin 2) ℂ) (hH : M.IsHermitian) (ha : 0 ≤ (M 0 0).re)
    (hc : 0 ≤ (M 1 1).re) (hd : Complex.normSq (M 0 1) ≤ (M 0 0).re * (M 1 1).re) : M.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hH, fun x => ?_⟩
  have h10 : M 1 0 = conj (M 0 1) := by
    have := congrFun (congrFun hH.eq 1) 0
    simpa [Matrix.conjTranspose_apply] using this.symm
  have h00 : M 0 0 = ((M 0 0).re : ℂ) := by
    have := congrFun (congrFun hH.eq 0) 0
    simp only [Matrix.conjTranspose_apply, RCLike.star_def] at this
    exact (Complex.conj_eq_iff_re.mp this).symm
  have h11 : M 1 1 = ((M 1 1).re : ℂ) := by
    have := congrFun (congrFun hH.eq 1) 1
    simp only [Matrix.conjTranspose_apply, RCLike.star_def] at this
    exact (Complex.conj_eq_iff_re.mp this).symm
  rw [Complex.nonneg_iff]
  have hd' : (M 0 1).re * (M 0 1).re + (M 0 1).im * (M 0 1).im ≤ (M 0 0).re * (M 1 1).re := by
    rw [Complex.normSq_apply] at hd; exact hd
  have hr := g58d_real2 _ _ _ _ (x 0).re (x 0).im (x 1).re (x 1).im ha hc hd'
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, h10, Pi.star_apply, RCLike.star_def]
  rw [h00, h11]
  constructor
  · simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.conj_re, Complex.conj_im]
    linarith
  · simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
    ring

theorem g58d_rank_le_one (M : Matrix (Fin 2) (Fin 2) ℂ) (h : M.det = 0) : M.rank ≤ 1 := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hk : 0 < Module.finrank ℂ (LinearMap.ker M.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, by simpa using hv⟩, by simpa using hv0⟩
  have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  simp only [Module.finrank_fin_fun] at this
  unfold Matrix.rank; omega

theorem g58d_rank_ne_zero (M : Matrix (Fin 2) (Fin 2) ℂ) (h : M ≠ 0) : M.rank ≠ 0 := by
  intro h0
  apply h
  unfold Matrix.rank at h0
  have h1 := Submodule.finrank_eq_zero.mp h0
  rw [LinearMap.range_eq_bot] at h1
  ext i j
  have := congrFun (LinearMap.congr_fun h1 (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

theorem solution (d : ℕ) (hd : 2 ≤ d) (b : BlockArray)
    (hb : b ∈ (cloningBlockSet d).extremePoints ℝ) :
    ∀ l v, (b l v).rank ≤ 1 ∧ (b l v ≠ 0 → (b l v).rank = 1) := by
  have hdet : ∀ l v, (b l v).det = 0 := by
    intro l v
    rw [mem_extremePoints] at hb
    obtain ⟨hmem, hext⟩ := hb
    obtain ⟨⟨hpsd, h1, h2, h3⟩, hsum⟩ := hmem
    fin_cases v
    · show (b l 0).det = 0
      by_contra hne
      have hB := hpsd l 0
      set B := b l 0 with hBdef
      have hH := hB.1
      have h10 : B 1 0 = conj (B 0 1) := by
        have := congrFun (congrFun hH.eq 1) 0
        simpa [Matrix.conjTranspose_apply] using this.symm
      have h00 : B 0 0 = ((B 0 0).re : ℂ) := by
        have := congrFun (congrFun hH.eq 0) 0
        simp only [Matrix.conjTranspose_apply, RCLike.star_def] at this
        exact (Complex.conj_eq_iff_re.mp this).symm
      have h11 : B 1 1 = ((B 1 1).re : ℂ) := by
        have := congrFun (congrFun hH.eq 1) 1
        simp only [Matrix.conjTranspose_apply, RCLike.star_def] at this
        exact (Complex.conj_eq_iff_re.mp this).symm
      have ha : 0 ≤ (B 0 0).re := (Complex.nonneg_iff.mp (hB.diag_nonneg (i := 0))).1
      have hc : 0 ≤ (B 1 1).re := (Complex.nonneg_iff.mp (hB.diag_nonneg (i := 1))).1
      set δ := (B 0 0).re * (B 1 1).re - Complex.normSq (B 0 1) with hδ
      have hdetδ : B.det = (δ : ℂ) := by
        rw [Matrix.det_fin_two, h10, Complex.mul_conj]
        conv_lhs => rw [h00, h11]
        rw [hδ]; push_cast; ring
      have hδpos : 0 < δ := by
        have h0 := hB.det_nonneg
        rw [hdetδ] at h0 hne
        have : (0 : ℝ) ≤ δ := Complex.zero_le_real.mp h0
        rcases this.lt_or_eq with h | h
        · exact h
        · exact absurd (by rw [← h]; simp) hne
      set βr := (B 0 1).re
      set h : ℝ := δ / (2 * |βr| + 1 + δ) with hh
      have hden : 0 < 2 * |βr| + 1 + δ := by positivity
      have hpos : 0 < h := div_pos hδpos hden
      have hle1 : h ≤ 1 := by rw [hh, div_le_one hden]; linarith [abs_nonneg βr]
      have hbound : h * (2 * |βr| + 1) ≤ δ := by
        rw [hh, div_mul_eq_mul_div, div_le_iff₀ hden]; nlinarith [abs_nonneg βr]
      let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
      let Z : BlockArray := fun l' v' => if l' = l ∧ v' = 0 then X else 0
      have hZd : ∀ l' v' (s : Fin 2), Z l' v' s s = 0 := by
        intro l' v' s; simp only [Z]; split_ifs
        · fin_cases s <;> simp [X]
        · simp
      have hl4 : d = 2 → l ≠ 4 := by
        intro hd2 hl; apply hne; rw [hBdef, hl, (h3 hd2).2 0]; simp
      have hmemσ : ∀ σ : ℝ, σ = 1 ∨ σ = -1 → b + (σ * h) • Z ∈ cloningBlockSet d := by
        intro σ hσ
        have hxe : ∀ l' v', (b + (σ * h) • Z) l' v' = b l' v' + (((σ * h : ℝ)) : ℂ) • Z l' v' := by
          intro l' v'; ext r c; simp [Complex.real_smul]
        refine ⟨⟨fun l' v' => ?_, fun l' => ?_, fun l' => ?_, fun hd2 => ⟨fun l' => ?_, fun v' => ?_⟩⟩,
          fun s => ?_⟩
        · rw [hxe]
          by_cases hc' : l' = l ∧ v' = 0
          · obtain ⟨rfl, rfl⟩ := hc'
            simp only [Z, and_self, if_true]
            apply g58d_psd2
            · refine hH.add ?_
              rw [Matrix.IsHermitian]; ext r c; fin_cases r <;> fin_cases c <;> simp [X, Matrix.conjTranspose_apply]
            · simp [X]; exact ha
            · simp [X]; exact hc
            · simp only [X, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
              simp
              rw [Complex.normSq_apply]
              simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
              have hn : Complex.normSq (B 0 1) = βr * βr + (B 0 1).im * (B 0 1).im := Complex.normSq_apply _
              have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
              have : σ * βr ≤ |βr| := by
                rcases hσ with rfl | rfl
                · simpa using le_abs_self βr
                · simpa using neg_abs_le βr |> fun h => by linarith
              have key : ((B 0 1).re + σ * h) * ((B 0 1).re + σ * h) + (B 0 1).im * (B 0 1).im ≤
                  (B 0 0).re * (B 1 1).re := by
                have e1 : ((B 0 1).re + σ * h) * ((B 0 1).re + σ * h) =
                    βr * βr + 2 * h * (σ * βr) + (σ * σ) * (h * h) := by ring
                rw [e1, hσ2]
                have := mul_le_mul_of_nonneg_left this hpos.le
                have := mul_le_mul_of_nonneg_left hle1 hpos.le
                nlinarith [abs_nonneg βr]
              simpa [Complex.mul_re, Complex.mul_im] using key
          · have : Z l' v' = 0 := by simp only [Z]; rw [if_neg hc']
            rw [this, smul_zero, add_zero]; exact hpsd l' v'
        · have : Z l' 1 = 0 := by simp [Z]
          rw [hxe, this, smul_zero, add_zero]; exact h1 l'
        · have : Z l' 2 = 0 := by simp [Z]
          rw [hxe, this, smul_zero, add_zero]; exact h2 l'
        · have : Z l' 2 = 0 := by simp [Z]
          rw [hxe, this, smul_zero, add_zero]; exact (h3 hd2).1 l'
        · have : Z 4 v' = 0 := by simp only [Z]; rw [if_neg (fun hh => hl4 hd2 hh.1.symm)]
          rw [hxe, this, smul_zero, add_zero]; exact (h3 hd2).2 v'
        · rw [← hsum s]
          refine Finset.sum_congr rfl (fun l' _ => Finset.sum_congr rfl (fun v' _ => ?_))
          rw [hxe]; simp [hZd]
      have hmid : b ∈ openSegment ℝ (b + (1 * h) • Z) (b + ((-1) * h) • Z) := by
        refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
        funext l' v'; ext r c
        simp [Complex.real_smul]; ring
      have heq := (hext _ (hmemσ 1 (Or.inl rfl)) _ (hmemσ (-1) (Or.inr rfl)) hmid).1
      have := congrFun (congrFun (congrFun (congrFun heq l) 0) 0) 1
      simp [Z, X, Complex.real_smul] at this
      exact hpos.ne' this
    · simp only [Fin.mk_one]
      rw [h1 l]; simp [Matrix.det_fin_two, coordinateProjector]
    · show (b l 2).det = 0
      rw [h2 l]; simp [Matrix.det_fin_two, coordinateProjector]
  intro l v
  have hr := g58d_rank_le_one _ (hdet l v)
  refine ⟨hr, fun hne => ?_⟩
  have := g58d_rank_ne_zero _ hne
  omega
