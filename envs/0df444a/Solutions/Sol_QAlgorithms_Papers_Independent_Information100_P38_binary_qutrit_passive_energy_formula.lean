-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P38.binary_qutrit_passive_energy_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:49:47.147255+00:00
-- url     : https://prove2.me/submissions/e98ea51b-5896-427e-9e89-534baf2912a0

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38
noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

namespace X6P38Qutrit

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P38

def rq {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) (v : EuclideanSpace ℂ (Fin d)) : ℝ :=
  (∑ i, ∑ j, conj (v i) * W i j * v j).re

def S {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) : Set ℝ :=
  {r | ∃ v : EuclideanSpace ℂ (Fin d), IsState v ∧ r = rq W v}

lemma lee_eq {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) : largestEnergyEigenvalue W = sSup (S W) := rfl

lemma state_sum {d : ℕ} (v : EuclideanSpace ℂ (Fin d)) (hv : IsState v) :
    ∑ i, ‖v i‖ ^ 2 = 1 := by
  unfold IsState at hv
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at hv
  simpa using hv

lemma S_bdd {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) : BddAbove (S W) := by
  refine ⟨∑ i, ∑ j, ‖W i j‖, ?_⟩
  rintro r ⟨v, hv, rfl⟩
  have h1 : ∀ i, ‖v i‖ ≤ 1 := fun i => by
    have := PiLp.norm_apply_le v i
    unfold IsState at hv; rw [hv] at this; exact this
  unfold rq
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have := h1 i; have := h1 j
  have := norm_nonneg (W i j); have := norm_nonneg (v i); have := norm_nonneg (v j)
  nlinarith [mul_le_mul_of_nonneg_left (h1 i) (norm_nonneg (W i j))]

lemma S_ne {d : ℕ} (hd : 0 < d) (W : Matrix (Fin d) (Fin d) ℂ) : (S W).Nonempty :=
  ⟨_, EuclideanSpace.single ⟨0, hd⟩ 1, by simp [IsState], rfl⟩

/-- Upper bound via a diagonalizing unitary. -/
lemma rq_le_of_diag {d : ℕ} (W V : Matrix (Fin d) (Fin d) ℂ) (hV : star V * V = 1)
    (μ : Fin d → ℝ) (hD : W = star V * Matrix.diagonal (fun i => (μ i : ℂ)) * V)
    (c : ℝ) (hc : ∀ i, μ i ≤ c) (v : EuclideanSpace ℂ (Fin d)) (hv : IsState v) :
    rq W v ≤ c := by
  have hq : ∀ (M : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ),
      (∑ i, ∑ j, conj (x i) * M i j * x j) = star x ⬝ᵥ (M *ᵥ x) := by
    intro M x
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def,
      mul_assoc]
  set x : Fin d → ℂ := fun i => v i
  set w := V *ᵥ x
  have hx : ∑ i, Complex.normSq (x i) = 1 := by
    have := state_sum v hv
    simpa [x, Complex.normSq_eq_norm_sq] using this
  have hw : ∑ i, Complex.normSq (w i) = 1 := by
    have e : ∀ y : Fin d → ℂ, ((∑ i, Complex.normSq (y i) : ℝ) : ℂ) = star y ⬝ᵥ y := by
      intro y
      simp [dotProduct, Complex.normSq_eq_conj_mul_self]
    have : star w ⬝ᵥ w = star x ⬝ᵥ x := by
      simp only [w, Matrix.star_mulVec]
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.star_eq_conjTranspose, hV,
        Matrix.vecMul_one]
    have h2 := e w
    rw [this, ← e x, hx] at h2
    exact_mod_cast h2
  have key : rq W v = ∑ i, μ i * Complex.normSq (w i) := by
    unfold rq
    rw [show (∑ i, ∑ j, conj (v i) * W i j * v j) = ∑ i, ∑ j, conj (x i) * W i j * x j from rfl,
      hq, hD]
    have : star x ⬝ᵥ ((star V * Matrix.diagonal (fun i => (μ i : ℂ)) * V) *ᵥ x) =
        star w ⬝ᵥ (Matrix.diagonal (fun i => (μ i : ℂ)) *ᵥ w) := by
      simp only [w, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_vecMul]
      simp [Matrix.star_eq_conjTranspose]
    rw [this]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.mul_re, Complex.normSq_apply, Complex.conj_re, Complex.conj_im]
    ring
  rw [key]
  calc _ ≤ ∑ i, c * Complex.normSq (w i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) (Complex.normSq_nonneg _)
    _ = c := by rw [← Finset.mul_sum, hw, mul_one]


lemma row_state {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (k : Fin d) :
    IsState (WithLp.toLp 2 (fun j => conj ((U : Matrix (Fin d) (Fin d) ℂ) k j)) :
      EuclideanSpace ℂ (Fin d)) := by
  unfold IsState
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp U.2) k) k
  rw [Matrix.mul_apply] at h
  simp only [Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  simp only [Complex.mul_conj, Complex.ofReal_re, Complex.one_re] at h2
  simpa [Complex.normSq_eq_norm_sq] using h2

lemma rq_row {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (k : Fin d) :
    rq W (WithLp.toLp 2 (fun j => conj ((U : Matrix (Fin d) (Fin d) ℂ) k j))) =
      (((U : Matrix (Fin d) (Fin d) ℂ) * W * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) k k).re := by
  unfold rq
  congr 1
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_conj,
    Finset.sum_mul]
  rw [Finset.sum_comm]

lemma passive3 (W : Matrix (Fin 3) (Fin 3) ℂ) (hW : W.IsHermitian) (htr : W.trace = 1) :
    passiveEnergy ![0, 1, 2] W = 1 - ergotropicSpectralWidth W := by
  unfold passiveEnergy ergotropicSpectralWidth
  rw [lee_eq, lee_eq]
  set l1 := sSup (S W)
  set l2 := sSup (S (-W))
  have hEE : ∀ Z : Matrix (Fin 3) (Fin 3) ℂ, Z.trace = 1 →
      energyExpectation ![0, 1, 2] Z = 1 - (Z 0 0).re + (Z 2 2).re := by
    intro Z hZ
    have := congrArg Complex.re hZ
    rw [Matrix.trace_fin_three] at this
    simp only [Complex.add_re, Complex.one_re] at this
    unfold energyExpectation
    simp [Fin.sum_univ_three]
    linarith
  have htrU : ∀ U : Matrix.unitaryGroup (Fin 3) ℂ,
      ((U : Matrix (Fin 3) (Fin 3) ℂ) * W * (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ).trace = 1 := by
    intro U
    rw [Matrix.trace_mul_comm, ← mul_assoc, ← Matrix.star_eq_conjTranspose,
      Unitary.star_mul_self_of_mem U.2, one_mul, htr]
  have hlow : ∀ U : Matrix.unitaryGroup (Fin 3) ℂ, 1 - (l1 + l2) ≤
      energyExpectation ![0, 1, 2] ((U : Matrix (Fin 3) (Fin 3) ℂ) * W *
        (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ) := by
    intro U
    rw [hEE _ (htrU U)]
    have h0 : (((U : Matrix (Fin 3) (Fin 3) ℂ) * W * (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ) 0 0).re
        ≤ l1 := le_csSup (S_bdd W) ⟨_, row_state U 0, (rq_row W U 0).symm⟩
    have h2 : -(((U : Matrix (Fin 3) (Fin 3) ℂ) * W * (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ) 2 2).re
        ≤ l2 := by
      refine le_csSup (S_bdd (-W)) ⟨_, row_state U 2, ?_⟩
      rw [rq_row]
      simp
    linarith
  -- attainment via the spectral theorem
  set E := hW.eigenvectorUnitary
  set μ := hW.eigenvalues
  have hdiag : star (E : Matrix (Fin 3) (Fin 3) ℂ) * W * (E : Matrix (Fin 3) (Fin 3) ℂ) =
      Matrix.diagonal (fun i => (μ i : ℂ)) := by
    have h := hW.conjStarAlgAut_star_eigenvectorUnitary
    simp at h
    exact h
  set σ : Equiv.Perm (Fin 3) := Fin.revPerm.trans (Tuple.sort μ)
  have hmono := Tuple.monotone_sort μ
  have hσ0 : ∀ i, μ (σ i) ≤ μ (σ 0) := fun i =>
    hmono (show Fin.rev i ≤ Fin.rev 0 by fin_cases i <;> decide)
  have hσ2 : ∀ i, μ (σ 2) ≤ μ (σ i) := fun i =>
    hmono (show Fin.rev 2 ≤ Fin.rev i by fin_cases i <;> decide)
  set V : Matrix (Fin 3) (Fin 3) ℂ := (star (E : Matrix (Fin 3) (Fin 3) ℂ)).submatrix σ id
  have hVs : star V = (E : Matrix (Fin 3) (Fin 3) ℂ).submatrix id σ := by
    simp [V, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
  have hVV : V * star V = 1 := by
    rw [hVs]
    ext i j
    simp only [V, Matrix.mul_apply, Matrix.submatrix_apply, id]
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M (σ i) (σ j))
      (Unitary.star_mul_self_of_mem E.2)
    simp only [Matrix.mul_apply] at h
    rw [h]
    simp [Matrix.one_apply, σ.injective.eq_iff]
  have hVV' : star V * V = 1 := mul_eq_one_comm.mp hVV
  have hVU : V ∈ Matrix.unitaryGroup (Fin 3) ℂ := Matrix.mem_unitaryGroup_iff.mpr hVV
  have hZ : V * W * star V = Matrix.diagonal (fun i => (μ (σ i) : ℂ)) := by
    rw [hVs]
    have : V * W * (E : Matrix (Fin 3) (Fin 3) ℂ).submatrix id σ =
        (star (E : Matrix (Fin 3) (Fin 3) ℂ) * W * (E : Matrix (Fin 3) (Fin 3) ℂ)).submatrix σ σ := by
      ext i j
      simp [V, Matrix.mul_apply]
    rw [this, hdiag, Matrix.submatrix_diagonal_equiv]
    rfl
  have hWd : W = star V * Matrix.diagonal (fun i => (μ (σ i) : ℂ)) * V := by
    rw [← hZ, ← mul_assoc, ← mul_assoc, hVV', one_mul, mul_assoc, hVV', mul_one]
  have hWd' : -W = star V * Matrix.diagonal (fun i => ((-μ (σ i) : ℝ) : ℂ)) * V := by
    rw [hWd]
    have : Matrix.diagonal (fun i => ((-μ (σ i) : ℝ) : ℂ)) =
        -Matrix.diagonal (fun i => (μ (σ i) : ℂ)) := by
      ext i j; simp [Matrix.diagonal_apply]; split_ifs <;> simp
    rw [this, Matrix.mul_neg, Matrix.neg_mul]
  have hl1 : l1 ≤ μ (σ 0) := csSup_le (S_ne (by norm_num) W) (by
    rintro r ⟨v, hv, rfl⟩
    exact rq_le_of_diag W V hVV' _ hWd _ hσ0 v hv)
  have hl2 : l2 ≤ -μ (σ 2) := csSup_le (S_ne (by norm_num) (-W)) (by
    rintro r ⟨v, hv, rfl⟩
    exact rq_le_of_diag (-W) V hVV' _ hWd' _ (fun i => neg_le_neg (hσ2 i)) v hv)
  have hatt : energyExpectation ![0, 1, 2] ((⟨V, hVU⟩ : Matrix.unitaryGroup (Fin 3) ℂ) *
      W * ((⟨V, hVU⟩ : Matrix.unitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)ᴴ) ≤
      1 - (l1 + l2) := by
    rw [hEE _ (htrU _)]
    show 1 - ((V * W * Vᴴ) 0 0).re + ((V * W * Vᴴ) 2 2).re ≤ _
    rw [← Matrix.star_eq_conjTranspose, hZ]
    simp
    linarith
  have hmem : energyExpectation ![0, 1, 2] ((⟨V, hVU⟩ : Matrix.unitaryGroup (Fin 3) ℂ) *
      W * ((⟨V, hVU⟩ : Matrix.unitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)ᴴ) ∈
      {r | ∃ U : Matrix.unitaryGroup (Fin 3) ℂ, r = energyExpectation ![0, 1, 2]
        ((U : Matrix (Fin 3) (Fin 3) ℂ) * W * (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ)} := ⟨_, rfl⟩
  apply le_antisymm
  · exact (csInf_le ⟨1 - (l1 + l2), by rintro r ⟨U, rfl⟩; exact hlow U⟩ hmem).trans hatt
  · exact le_csInf ⟨_, hmem⟩ (by rintro r ⟨U, rfl⟩; exact hlow U)


lemma rq_affine {d : ℕ} (a c : ℝ) (W : Matrix (Fin d) (Fin d) ℂ) (v : EuclideanSpace ℂ (Fin d))
    (hv : IsState v) : rq ((a : ℂ) • 1 + (c : ℂ) • W) v = a + c * rq W v := by
  have hs := state_sum v hv
  unfold rq
  have e : (∑ i, ∑ j, conj (v i) * ((a : ℂ) • 1 + (c : ℂ) • W) i j * v j) =
      (a : ℂ) * ∑ i, ((‖v i‖ ^ 2 : ℝ) : ℂ) + (c : ℂ) * ∑ i, ∑ j, conj (v i) * W i j * v j := by
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_add,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_ite, mul_one, mul_zero, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.ofReal_pow, ← Complex.mul_conj', mul_comm (v i)]
      ring
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
  rw [e, ← Complex.ofReal_sum, hs, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  simp

lemma lee_affine {d : ℕ} (hd : 0 < d) (a c : ℝ) (hc : 0 ≤ c) (W : Matrix (Fin d) (Fin d) ℂ) :
    largestEnergyEigenvalue ((a : ℂ) • 1 + (c : ℂ) • W) = a + c * largestEnergyEigenvalue W := by
  rw [lee_eq, lee_eq]
  have hS : S ((a : ℂ) • 1 + (c : ℂ) • W) = (fun r => a + c * r) '' S W := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨rq W v, ⟨v, hv, rfl⟩, (rq_affine a c W v hv).symm⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, (rq_affine a c W v hv).symm⟩
  rw [hS]
  refine (Monotone.map_csSup_of_continuousAt ?_ ?_ (S_ne hd W) (S_bdd W)).symm
  · exact (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
  · intro x y hxy
    simp only
    nlinarith

lemma lee_diag3 (r : Fin 3 → ℝ) :
    largestEnergyEigenvalue (Matrix.diagonal fun i => (r i : ℂ)) = max (r 0) (max (r 1) (r 2)) := by
  rw [lee_eq]
  apply le_antisymm
  · refine csSup_le (S_ne (by norm_num) _) ?_
    rintro x ⟨v, hv, rfl⟩
    refine rq_le_of_diag _ 1 (by simp) r (by simp) _ ?_ v hv
    intro i
    fin_cases i <;> simp
  · have h : ∀ i, r i ∈ S (Matrix.diagonal fun i => (r i : ℂ)) := by
      intro i
      refine ⟨EuclideanSpace.single i 1, by simp [IsState], ?_⟩
      simp [rq, Matrix.diagonal_apply]
    have b := S_bdd (Matrix.diagonal fun i => (r i : ℂ))
    exact max_le (le_csSup b (h 0)) (max_le (le_csSup b (h 1)) (le_csSup b (h 2)))

end X6P38Qutrit

open X6P38Qutrit QAlgorithms QAlgorithms.Papers.Independent.Information100.P38 in
theorem solution (A X : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : IsEffect A) (hX : IsDensityMatrix X) (hV0 : 0 < A.trace.re) (hV3 : A.trace.re < 3) :
    let V := A.trace.re
    let t := effectProb A X
    let D := ergotropicSpectralWidth A
    let Y := ergotropicCoarseGraining (ergotropicBinary A) X
    (∀ W : Matrix (Fin 3) (Fin 3) ℂ, IsDensityMatrix W →
      passiveEnergy ![0, 1, 2] W = 1 - ergotropicSpectralWidth W) ∧
    Y = (((1 - t) / (3 - V) : ℝ) : ℂ) • 1 +
      (((t / V - (1 - t) / (3 - V)) : ℝ) : ℂ) • A ∧
    ergotropicSpectralWidth Y = D * |3*t - V| / (V * (3 - V)) ∧
    passiveEnergy ![0, 1, 2] Y = 1 - D * |3*t - V| / (V * (3 - V)) ∧
    passiveEnergy ![0, 1, 2] (energyDephasing X) = 1 - qutritPopulationWidth X ∧
    passiveEnergy ![0, 1, 2] (energyDephasing X) - passiveEnergy ![0, 1, 2] Y =
      D * |3*t - V| / (V * (3 - V)) - qutritPopulationWidth X := by
  intro V t D Y
  have hAh : A.IsHermitian := hA.1.isHermitian
  have hXh : X.IsHermitian := hX.1.isHermitian
  have realOf : ∀ z : ℂ, star z = z → z = (z.re : ℂ) := fun z hz =>
    (Complex.conj_eq_iff_re.mp hz).symm
  have hTA : A.trace = (V : ℂ) :=
    realOf _ (by rw [← Matrix.trace_conjTranspose, hAh.eq])
  have hTAX : (A * X).trace = (t : ℂ) := by
    refine realOf _ ?_
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hAh.eq, hXh.eq,
      Matrix.trace_mul_comm]
  have hT1AX : ((1 - A) * X).trace = ((1 - t : ℝ) : ℂ) := by
    rw [Matrix.sub_mul, one_mul, Matrix.trace_sub, hX.2, hTAX]; push_cast; ring
  have hT1A : (1 - A).trace = ((3 - V : ℝ) : ℂ) := by
    rw [Matrix.trace_sub, hTA, Matrix.trace_one]; push_cast; simp
  have hVne : (V : ℂ) ≠ 0 := by exact_mod_cast hV0.ne'
  have h3Vne : ((3 - V : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hV3).ne'
  have hVr : V ≠ 0 := ne_of_gt (show 0 < V from hV0)
  have h3Vr : 3 - V ≠ 0 := ne_of_gt (show 0 < 3 - V from sub_pos.mpr hV3)
  set a : ℝ := (1 - t) / (3 - V)
  set b : ℝ := t / V - (1 - t) / (3 - V)
  have hY : Y = (a : ℂ) • 1 + (b : ℂ) • A := by
    simp only [Y, ergotropicCoarseGraining, ergotropicBinary, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hTA, hTAX, hT1AX, hT1A, hVne, h3Vne, if_false]
    simp only [a, b]
    push_cast
    rw [smul_sub]
    module
  -- spectral width of Y
  have hb : b = (3 * t - V) / (V * (3 - V)) := by
    simp only [b]
    field_simp
    ring
  have hwY : ergotropicSpectralWidth Y = |b| * D := by
    unfold ergotropicSpectralWidth
    simp only [D, ergotropicSpectralWidth]
    rcases le_or_gt 0 b with h | h
    · have e1 : -Y = ((-a : ℝ) : ℂ) • 1 + (b : ℂ) • (-A) := by rw [hY]; push_cast; module
      rw [e1, hY, lee_affine (by norm_num) _ _ h, lee_affine (by norm_num) _ _ h, abs_of_nonneg h]
      ring
    · have e1 : Y = (a : ℂ) • 1 + ((-b : ℝ) : ℂ) • (-A) := by rw [hY]; push_cast; module
      have e2 : -Y = ((-a : ℝ) : ℂ) • 1 + ((-b : ℝ) : ℂ) • A := by rw [hY]; push_cast; module
      rw [e2, e1, lee_affine (by norm_num) _ _ (by linarith),
        lee_affine (by norm_num) _ _ (by linarith), abs_of_neg h]
      ring
  have hwY' : ergotropicSpectralWidth Y = D * |3 * t - V| / (V * (3 - V)) := by
    rw [hwY, hb, abs_div, abs_of_pos (mul_pos hV0 (sub_pos.mpr hV3))]
    ring
  -- Y is Hermitian of trace one
  have hYh : Y.IsHermitian := by
    rw [hY]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hAh.eq]
    simp
  have hYt : Y.trace = 1 := by
    rw [hY, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, hTA]
    have : 3 * a + b * V = 1 := by
      simp only [a, b]
      field_simp
      ring
    have h2 : ((3 * a + b * V : ℝ) : ℂ) = 1 := by rw [this]; simp
    rw [← h2]
    simp only [Fintype.card_fin, smul_eq_mul]
    push_cast
    ring
  -- dephased input
  set r : Fin 3 → ℝ := fun i => (X i i).re
  have hdeph : energyDephasing X = Matrix.diagonal fun i => (r i : ℂ) := by
    unfold energyDephasing
    congr 1
    funext i
    exact realOf _ (hXh.apply i i)
  have hdh : (energyDephasing X).IsHermitian := by
    rw [hdeph]
    unfold Matrix.IsHermitian
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  have hdt : (energyDephasing X).trace = 1 := by
    unfold energyDephasing
    rw [Matrix.trace_diagonal]
    exact hX.2
  have hwd : ergotropicSpectralWidth (energyDephasing X) = qutritPopulationWidth X := by
    unfold ergotropicSpectralWidth qutritPopulationWidth
    have e : -energyDephasing X = Matrix.diagonal fun i => ((-r i : ℝ) : ℂ) := by
      rw [hdeph]
      ext i j
      simp only [Matrix.neg_apply, Matrix.diagonal_apply]
      split_ifs <;> simp
    rw [e, hdeph, lee_diag3, lee_diag3 (fun i => -r i)]
    simp only [r, max_neg_neg]
    ring
  have hPY := passive3 Y hYh hYt
  have hPd := passive3 _ hdh hdt
  refine ⟨fun W hW => passive3 W hW.1.isHermitian hW.2, ?_, hwY', ?_, ?_, ?_⟩
  · rw [hY]
  · rw [hPY, hwY']
  · rw [hPd, hwd]
  · rw [hPd, hwd, hPY, hwY']
    ring
