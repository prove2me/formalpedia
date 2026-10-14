-- Prove2me | solution 1 for PathFindingLP.WeightFunction.slack_sensitivity_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T20:58:02.761231+00:00
-- url     : https://prove2.me/submissions/5672fc4d-5317-4652-aca6-5302d0ccefb9

import Mathlib
import Definitions.Def_PathFindingLP_WeightFunction_RegularizedObjective
import Definitions.Def_PathFindingLP_WeightFunction_SlackSensitivity

set_option autoImplicit false

open Matrix

/-- `N(e) = Aᵀ diag(e) A`. -/
noncomputable def scN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (e : Fin m → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Aᵀ * diagonal e * A

/-- `Q(e) = A N(e)⁻¹ Aᵀ`. -/
noncomputable def scQm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (e : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  A * (scN A e)⁻¹ * Aᵀ

/-- Leverage-type scores `τ_i(e) = e_i Q_ii(e)`. -/
noncomputable def scT {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (e : Fin m → ℝ) : Fin m → ℝ :=
  fun i => e i * scQm A e i i



/-- `e_i = w_i^α / s_i²`. -/
noncomputable def scE {m : ℕ} (α : ℝ) (s w : Fin m → ℝ) : Fin m → ℝ :=
  fun i => w i ^ α * ((s i)⁻¹) ^ 2

lemma pfw_mulVec_injective {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) :
    Function.Injective A.mulVec := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fin_fun] at h
  have hk : Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 0 := by
    unfold Matrix.rank at hA; omega
  have hb : LinearMap.ker A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hk
  have := LinearMap.ker_eq_bot.mp hb
  exact fun x y h => this h

lemma scN_posDef {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n)
    (e : Fin m → ℝ) (he : ∀ i, 0 < e i) : (scN A e).PosDef := by
  have hD : (diagonal e).PosDef := Matrix.posDef_diagonal_iff.mpr he
  have := hD.conjTranspose_mul_mul_same (pfw_mulVec_injective A hA)
  simpa [scN, Matrix.conjTranspose_eq_transpose_of_trivial] using this

lemma scN_isUnit {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n)
    (e : Fin m → ℝ) (he : ∀ i, 0 < e i) : IsUnit (scN A e).det :=
  isUnit_iff_ne_zero.mpr (scN_posDef A hA e he).det_pos.ne'

lemma scQm_psd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (e : Fin m → ℝ) (he : ∀ i, 0 ≤ e i) :
    (scQm A e).PosSemidef := by
  have hN : (scN A e).PosSemidef := by
    have hD : (diagonal e).PosSemidef := Matrix.PosSemidef.diagonal (fun i => he i)
    have := hD.conjTranspose_mul_mul_same A
    simpa [scN, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have := hN.inv.mul_mul_conjTranspose_same A
  simpa [scQm, Matrix.conjTranspose_eq_transpose_of_trivial] using this

lemma scQm_idem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (e : Fin m → ℝ)
    (hu : IsUnit (scN A e).det) : scQm A e * diagonal e * scQm A e = scQm A e := by
  unfold scQm
  have h : A * (scN A e)⁻¹ * Aᵀ * diagonal e * (A * (scN A e)⁻¹ * Aᵀ)
      = A * ((scN A e)⁻¹ * (Aᵀ * diagonal e * A) * (scN A e)⁻¹) * Aᵀ := by
    simp only [Matrix.mul_assoc]
  rw [h, show Aᵀ * diagonal e * A = scN A e from rfl, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul]

/-- Rank-one update with the explicit leverage term. -/
lemma sc_det_affine {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin m → ℝ) (i : Fin m)
    (hM : IsUnit (Bᵀ * diagonal d * B).det) (c : ℝ) :
    (Bᵀ * diagonal (Function.update d i (d i + c)) * B).det =
      (Bᵀ * diagonal d * B).det * (1 + c * (B * (Bᵀ * diagonal d * B)⁻¹ * Bᵀ) i i) := by
  have hr1 : Bᵀ * diagonal (Function.update d i (d i + c)) * B =
      Bᵀ * diagonal d * B + replicateCol Unit (c • (fun k => B i k)) *
        replicateRow Unit (fun k => B i k) := by
    ext k l
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, diagonal_apply,
      replicateCol_apply, replicateRow_apply, Pi.smul_apply, smul_eq_mul]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.univ_unique, Finset.sum_singleton]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [Function.update_self]
    have : ∑ x ∈ Finset.univ.erase i, B x k * Function.update d i (d i + c) x * B x l
        = ∑ x ∈ Finset.univ.erase i, B x k * d x * B x l := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
    rw [this]
    ring
  rw [hr1, det_add_replicateCol_mul_replicateRow hM]
  congr 1
  rw [Matrix.det_unique]
  have : replicateCol Unit (c • (fun k => B i k)) = c • replicateCol Unit (fun k => B i k) := by
    ext; simp
  rw [this, Matrix.mul_smul]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply_eq]
  congr 2

lemma sc_sum_update {m : ℕ} (f : Fin m → ℝ) (i : Fin m) (x : ℝ) :
    ∑ j, Function.update f i x j = ∑ j, f j - f i + x := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    Finset.sdiff_singleton_eq_erase]
  ring

open PathFindingLP.WeightFunction in
/-- First-order condition: a minimizer satisfies `w_i = τ_i + β`. -/
theorem sc_foc {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) (α β : ℝ)
    (hα : 0 < α) (s w : Fin m → ℝ) (hs : ∀ i, 0 < s i)
    (hw : IsRegularizedMinimizer A α β s w) (i : Fin m) :
    w i = scT A (scE α s w) i + β := by
  obtain ⟨hwpos, hmin⟩ := hw
  set B := diagonal (fun i => (s i)⁻¹) * A with hB
  set d : Fin m → ℝ := fun j => w j ^ α with hd
  have hdpos : ∀ j, 0 < d j := fun j => Real.rpow_pos_of_pos (hwpos j) α
  -- the matrix of fhat is N(e)
  have hMN : Bᵀ * diagonal d * B = scN A (scE α s w) := by
    rw [hB, scN, Matrix.transpose_mul, diagonal_transpose]
    have : Aᵀ * diagonal (fun i => (s i)⁻¹) * diagonal d * (diagonal (fun i => (s i)⁻¹) * A)
        = Aᵀ * (diagonal (fun i => (s i)⁻¹) * diagonal d * diagonal (fun i => (s i)⁻¹)) * A := by
      simp only [Matrix.mul_assoc]
    rw [this, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 3; funext j; simp only [scE, hd]; ring
  have he : ∀ j, 0 < scE α s w j := fun j =>
    mul_pos (Real.rpow_pos_of_pos (hwpos j) α) (pow_pos (inv_pos.mpr (hs j)) 2)
  have hMu : IsUnit (Bᵀ * diagonal d * B).det := by rw [hMN]; exact scN_isUnit A hA _ he
  set D := (Bᵀ * diagonal d * B).det with hD
  have hDpos : 0 < D := by rw [hD, hMN]; exact (scN_posDef A hA _ he).det_pos
  set q := (B * (Bᵀ * diagonal d * B)⁻¹ * Bᵀ) i i with hq
  -- q = s_i⁻² Q_ii
  have hqQ : w i ^ α * q = scT A (scE α s w) i := by
    rw [hq, hMN, scT, scQm, hB, Matrix.transpose_mul, diagonal_transpose]
    have : diagonal (fun i => (s i)⁻¹) * A * (scN A (scE α s w))⁻¹ *
        (Aᵀ * diagonal (fun i => (s i)⁻¹))
        = diagonal (fun i => (s i)⁻¹) * (A * (scN A (scE α s w))⁻¹ * Aᵀ) *
          diagonal (fun i => (s i)⁻¹) := by simp only [Matrix.mul_assoc]
    rw [this, Matrix.mul_diagonal, Matrix.diagonal_mul, scE]
    ring
  -- the one-dimensional function
  let φ : ℝ → ℝ := fun t => fhat A α β s (Function.update w i (w i + t))
  have hφ : ∀ t, φ t = (∑ j, w j + t)
      - (1 / α) * Real.log (D * (1 + ((w i + t) ^ α - w i ^ α) * q))
      - β * (∑ j, Real.log (w j) - Real.log (w i) + Real.log (w i + t)) := by
    intro t
    simp only [φ, fhat]
    have h1 : (fun j => Function.update w i (w i + t) j ^ α)
        = Function.update d i (d i + ((w i + t) ^ α - w i ^ α)) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [hd]
      · simp [Function.update_of_ne hj, hd]
    have h2 : (fun j => Real.log (Function.update w i (w i + t) j))
        = Function.update (fun j => Real.log (w j)) i (Real.log (w i + t)) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    rw [h1, sc_det_affine B d i hMu, sc_sum_update, show (∑ j, Real.log (Function.update w i
      (w i + t) j)) = ∑ j, Function.update (fun j => Real.log (w j)) i (Real.log (w i + t)) j
      from by rw [← h2], sc_sum_update]
    ring
  -- local minimum at 0
  have hloc : IsLocalMin φ 0 := by
    have hmem : Set.Ioo (-w i) (w i) ∈ nhds (0 : ℝ) :=
      Ioo_mem_nhds (by linarith [hwpos i]) (hwpos i)
    filter_upwards [hmem] with t ht
    have hpos : ∀ j, 0 < Function.update w i (w i + t) j := by
      intro j
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; linarith [ht.1]
      · rw [Function.update_of_ne hj]; exact hwpos j
    have h0 : φ 0 = fhat A α β s w := by simp [φ]
    rw [h0]; exact hmin _ hpos
  -- derivative at 0
  have hderiv : HasDerivAt φ (1 - (1 / α) * (D * (1 * α * w i ^ (α - 1) * q) / D)
      - β * (1 / w i)) 0 := by
    have hfun : φ = fun t => (∑ j, w j + t)
        - (1 / α) * Real.log (D * (1 + ((w i + t) ^ α - w i ^ α) * q))
        - β * (∑ j, Real.log (w j) - Real.log (w i) + Real.log (w i + t)) := funext hφ
    rw [hfun]
    have hlin : HasDerivAt (fun t : ℝ => w i + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (w i)
    have hrp : HasDerivAt (fun t : ℝ => (w i + t) ^ α) (1 * α * (w i + 0) ^ (α - 1)) 0 :=
      hlin.rpow_const (Or.inl (by simp; exact (hwpos i).ne'))
    have hin : HasDerivAt (fun t : ℝ => D * (1 + ((w i + t) ^ α - w i ^ α) * q))
        (D * (1 * α * w i ^ (α - 1) * q)) 0 := by
      have := ((hrp.sub_const (w i ^ α)).mul_const q).const_add 1 |>.const_mul D
      simpa using this
    have hlog : HasDerivAt (fun t : ℝ => Real.log (D * (1 + ((w i + t) ^ α - w i ^ α) * q)))
        (D * (1 * α * w i ^ (α - 1) * q) / D) 0 := by
      have := hin.log (by simp; exact hDpos.ne')
      simpa using this
    have hlog2 : HasDerivAt (fun t : ℝ => Real.log (w i + t)) (1 / w i) 0 := by
      have := hlin.log (by simp; exact (hwpos i).ne')
      simpa using this
    have := (((hasDerivAt_id (0 : ℝ)).const_add (∑ j, w j)).sub
      (hlog.const_mul (1 / α))).sub
      ((hlog2.const_add (∑ j, Real.log (w j) - Real.log (w i))).const_mul β)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply, id]
  have hzero := hloc.hasDerivAt_eq_zero hderiv
  have hwi := (hwpos i).ne'
  have hrp1 : w i ^ (α - 1) = w i ^ α / w i := Real.rpow_sub_one hwi α
  rw [hrp1] at hzero
  rw [← hqQ]
  field_simp at hzero
  linarith


/-- Quadratic form of `N(d) = Aᵀ diag(d) A`. -/
lemma ss_quad {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d : Fin m → ℝ) (u : Fin n → ℝ) :
    u ⬝ᵥ (scN A d *ᵥ u) = ∑ j, d j * (A *ᵥ u) j ^ 2 := by
  rw [scN, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  simp only [dotProduct, mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Diagonal entry of `A N Aᵀ` as a quadratic form. -/
lemma ss_Qii {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (N : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin m) : (A * N * Aᵀ) i i = (fun k => A i k) ⬝ᵥ (N *ᵥ (fun k => A i k)) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, mulVec, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

/-- Loewner comparison of inverses: `c N2 ≤ N1` gives `N1⁻¹ ≤ c⁻¹ N2⁻¹` on quadratic forms. -/
lemma ss_inv_le {n : ℕ} (N1 N2 : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 < c)
    (h1 : IsUnit N1.det) (h2 : IsUnit N2.det) (hs : N2ᵀ = N2)
    (hpos : ∀ v, 0 ≤ v ⬝ᵥ (N2 *ᵥ v))
    (hle : ∀ v, c * (v ⬝ᵥ (N2 *ᵥ v)) ≤ v ⬝ᵥ (N1 *ᵥ v)) (x : Fin n → ℝ) :
    x ⬝ᵥ (N1⁻¹ *ᵥ x) ≤ c⁻¹ * (x ⬝ᵥ (N2⁻¹ *ᵥ x)) := by
  set u := N1⁻¹ *ᵥ x with hu_def
  set y := N2⁻¹ *ᵥ x with hy_def
  have hu : N1 *ᵥ u = x := by
    rw [hu_def, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h1, Matrix.one_mulVec]
  have hy : N2 *ᵥ y = x := by
    rw [hy_def, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h2, Matrix.one_mulVec]
  have hyu : y ⬝ᵥ (N2 *ᵥ u) = x ⬝ᵥ u := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, hy]
  have h0 := hpos (u - c⁻¹ • y)
  have e1 : (u - c⁻¹ • y) ⬝ᵥ (N2 *ᵥ (u - c⁻¹ • y)) = u ⬝ᵥ (N2 *ᵥ u) - c⁻¹ * (u ⬝ᵥ x)
      - c⁻¹ * (x ⬝ᵥ u) + c⁻¹ * c⁻¹ * (y ⬝ᵥ x) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hy, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hyu]
    ring
  rw [e1] at h0
  have h3 := hle u
  rw [hu] at h3
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
  have hux : u ⬝ᵥ x = x ⬝ᵥ u := dotProduct_comm _ _
  have hyx : y ⬝ᵥ x = x ⬝ᵥ y := dotProduct_comm _ _
  have h4 : 0 ≤ c * (u ⬝ᵥ (N2 *ᵥ u) - c⁻¹ * (u ⬝ᵥ x) - c⁻¹ * (x ⬝ᵥ u)
      + c⁻¹ * c⁻¹ * (y ⬝ᵥ x)) := mul_nonneg hc.le h0
  have h5 : c * (u ⬝ᵥ (N2 *ᵥ u) - c⁻¹ * (u ⬝ᵥ x) - c⁻¹ * (x ⬝ᵥ u)
      + c⁻¹ * c⁻¹ * (y ⬝ᵥ x)) = c * (u ⬝ᵥ (N2 *ᵥ u)) - (c * c⁻¹) * (u ⬝ᵥ x)
      - (c * c⁻¹) * (x ⬝ᵥ u) + (c * c⁻¹) * c⁻¹ * (y ⬝ᵥ x) := by ring
  rw [h5, hcc] at h4
  rw [hux, hyx] at h4
  linarith

/-- Leverage scores lie in `[0, 1]`. -/
lemma ss_tau {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n)
    (e : Fin m → ℝ) (he : ∀ i, 0 < e i) (i : Fin m) :
    0 ≤ scT A e i ∧ scT A e i ≤ 1 := by
  have hQ := scQm_psd A e (fun j => (he j).le)
  have hid := scQm_idem A e (scN_isUnit A hA e he)
  set Q := scQm A e with hQdef
  have hdiag : 0 ≤ Q i i := hQ.diag_nonneg
  have hsym : ∀ j, Q j i = Q i j := fun j => by
    have := hQ.isHermitian.apply i j
    simpa using this
  have hsum : Q i i = ∑ j, e j * Q i j ^ 2 := by
    conv_lhs => rw [← hid]
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_diagonal, hsym j]
    ring
  have hge : e i * Q i i ^ 2 ≤ Q i i := by
    have := Finset.single_le_sum (f := fun j => e j * Q i j ^ 2)
      (fun j _ => mul_nonneg (he j).le (sq_nonneg _)) (Finset.mem_univ i)
    rw [← hsum] at this
    exact this
  have hT : scT A e i = e i * Q i i := rfl
  rw [hT]
  have ht0 : 0 ≤ e i * Q i i := mul_nonneg (he i).le hdiag
  refine ⟨ht0, ?_⟩
  have : (e i * Q i i) ^ 2 ≤ e i * Q i i := by
    have := mul_le_mul_of_nonneg_left hge (he i).le
    nlinarith
  nlinarith

open PathFindingLP.WeightFunction in
/-- Each term of the slack sensitivity. -/
lemma ss_term {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ)
    (hw : ∀ i, 0 < w i) (i : Fin m) :
    matNorm (projMatrix A s w) (diagonal (fun j => (Real.sqrt (w j))⁻¹) *ᵥ Pi.single i 1)
      = Real.sqrt ((s i)⁻¹ ^ 2 * scQm A (fun j => w j * (s j)⁻¹ ^ 2) i i) := by
  unfold matNorm
  congr 1
  have hM : Aᵀ * diagonal (fun i => (s i)⁻¹) * diagonal w * diagonal (fun i => (s i)⁻¹) * A
      = scN A (fun j => w j * (s j)⁻¹ ^ 2) := by
    rw [scN]
    have : Aᵀ * diagonal (fun i => (s i)⁻¹) * diagonal w * diagonal (fun i => (s i)⁻¹) * A
        = Aᵀ * (diagonal (fun i => (s i)⁻¹) * diagonal w * diagonal (fun i => (s i)⁻¹)) * A := by
      simp only [Matrix.mul_assoc]
    rw [this, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 2; exact congrArg diagonal (funext fun j => by ring)
  have hP : projMatrix A s w = diagonal (fun i => Real.sqrt (w i)) *
      (diagonal (fun i => (s i)⁻¹) * scQm A (fun j => w j * (s j)⁻¹ ^ 2) *
        diagonal (fun i => (s i)⁻¹)) * diagonal (fun i => Real.sqrt (w i)) := by
    unfold projMatrix
    rw [hM, scQm]
    simp only [Matrix.mul_assoc]
  have hv : diagonal (fun j => (Real.sqrt (w j))⁻¹) *ᵥ Pi.single i 1
      = Pi.single i (Real.sqrt (w i))⁻¹ := by
    funext k
    rw [mulVec_diagonal]
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [hv, hP]
  have hsq : Real.sqrt (w i) ≠ 0 := (Real.sqrt_pos.mpr (hw i)).ne'
  simp only [single_dotProduct, mulVec, dotProduct_single]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_mul]
  field_simp

open PathFindingLP.WeightFunction in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.rank = n) (hn : 0 < n) (hnm : n < m) (s : Fin m → ℝ) (hs : ∀ i, 0 < s i)
    (w : Fin m → ℝ) (hw : IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s w) :
    slackSensitivity A s w ≤ 2 := by
  have hm : 0 < m := lt_trans hn hnm
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (n : ℝ) < m := by exact_mod_cast hnm
  set X : ℝ := 2 * (m : ℝ) / (n : ℝ) with hX
  have hX2 : 2 < X := by
    rw [hX, lt_div_iff₀ hnR]; linarith
  set L : ℝ := Real.logb 2 X with hLdef
  have hL : 1 < L := by
    rw [hLdef, Real.lt_logb_iff_rpow_lt (by norm_num) (by linarith)]
    simpa using hX2
  have hLpos : 0 < L := by linarith
  set α := thm1Alpha A with hαdef
  set β := thm1Beta A with hβdef
  have hα : α = 1 - L⁻¹ := by
    rw [hαdef, thm1Alpha, hA]
  have hβ : β = (n : ℝ) / (2 * (m : ℝ)) := by
    rw [hβdef, thm1Beta, hA]
  have hLinv : L⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL
  have hLinv0 : 0 < L⁻¹ := inv_pos.mpr hLpos
  have h1α : 1 - α = L⁻¹ := by rw [hα]; ring
  have hαpos : 0 < α := by rw [hα]; linarith
  have hβpos : 0 < β := by rw [hβ]; positivity
  have hβle : β ≤ 1 := by
    rw [hβ, div_le_one (by positivity)]; linarith
  -- β^(1-α) = 1/2
  have hhalf : β ^ (1 - α) = 1 / 2 := by
    rw [h1α, Real.rpow_def_of_pos hβpos]
    have hβX : β = X⁻¹ := by rw [hβ, hX]; field_simp
    have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
    have hL' : L = Real.log X / Real.log 2 := by rw [hLdef, Real.logb]
    rw [hβX, Real.log_inv, hL']
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : -Real.log X * (Real.log X / Real.log 2)⁻¹ = -Real.log 2 := by
      field_simp
    rw [this, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have hwpos := hw.1
  set e := scE α s w with he_def
  have hepos : ∀ j, 0 < e j := fun j =>
    mul_pos (Real.rpow_pos_of_pos (hwpos j) α) (pow_pos (inv_pos.mpr (hs j)) 2)
  set f : Fin m → ℝ := fun j => w j * (s j)⁻¹ ^ 2 with hf_def
  have hfpos : ∀ j, 0 < f j := fun j => mul_pos (hwpos j) (pow_pos (inv_pos.mpr (hs j)) 2)
  have hfoc : ∀ j, w j = scT A e j + β := fun j => sc_foc A hA α β hαpos s w hs hw j
  have hwβ : ∀ j, β ≤ w j := fun j => by
    have := (ss_tau A hA e hepos j).1; rw [hfoc j]; linarith
  have hsplit : ∀ j, w j = w j ^ α * w j ^ (1 - α) := fun j => by
    rw [← Real.rpow_add (hwpos j)]; simp
  have hhalfw : ∀ j, 1 / 2 ≤ w j ^ (1 - α) := fun j => by
    rw [← hhalf]
    exact Real.rpow_le_rpow hβpos.le (hwβ j) (by linarith)
  have hcmp : ∀ j, (1 / 2) * e j ≤ f j := fun j => by
    have hs2 : 0 ≤ (s j)⁻¹ ^ 2 := sq_nonneg _
    have hwa : 0 < w j ^ α := Real.rpow_pos_of_pos (hwpos j) α
    have : (1 / 2) * w j ^ α ≤ w j := by
      have h := mul_le_mul_of_nonneg_left (hhalfw j) hwa.le
      rw [← hsplit j] at h
      linarith
    simp only [he_def, hf_def, scE]
    nlinarith
  -- comparison of the two inverse quadratic forms
  have hNe := scN_isUnit A hA e hepos
  have hNf := scN_isUnit A hA f hfpos
  have hsymm : (scN A e)ᵀ = scN A e := by
    simp [scN, Matrix.transpose_mul, Matrix.mul_assoc]
  have hposq : ∀ v, 0 ≤ v ⬝ᵥ (scN A e *ᵥ v) := fun v => by
    rw [ss_quad]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hepos j).le (sq_nonneg _))
  have hleq : ∀ v, (1 / 2) * (v ⬝ᵥ (scN A e *ᵥ v)) ≤ v ⬝ᵥ (scN A f *ᵥ v) := fun v => by
    rw [ss_quad, ss_quad, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have := mul_le_mul_of_nonneg_right (hcmp j) (sq_nonneg ((A *ᵥ v) j))
    linarith
  apply ciSup_le
  intro i
  rw [ss_term A s w hwpos i]
  have hQ : scQm A f i i ≤ 2 * scQm A e i i := by
    rw [scQm, scQm, ss_Qii, ss_Qii]
    have := ss_inv_le (scN A f) (scN A e) (1 / 2) (by norm_num) hNf hNe hsymm hposq hleq
      (fun k => A i k)
    simpa using this
  -- the scalar bound
  have hτ := ss_tau A hA e hepos i
  set q := (s i)⁻¹ ^ 2 * scQm A e i i with hq
  have hτq : scT A e i = w i ^ α * q := by
    simp only [scT, he_def, scE, hq]; ring
  have hwa : 0 < w i ^ α := Real.rpow_pos_of_pos (hwpos i) α
  have hqle : q ≤ w i ^ (1 - α) := by
    have h1 : w i ^ α * q ≤ w i ^ α * w i ^ (1 - α) := by
      rw [← hτq, ← hsplit i, hfoc i]; linarith
    exact le_of_mul_le_mul_left h1 hwa
  have hw2 : w i ≤ 2 := by rw [hfoc i]; linarith [hτ.2]
  have hpow2 : w i ^ (1 - α) ≤ 2 := by
    rcases le_or_gt (w i) 1 with h | h
    · have := Real.rpow_le_one (hwpos i).le h (by linarith : (0:ℝ) ≤ 1 - α)
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le h.le (by linarith : 1 - α ≤ 1)
      rw [Real.rpow_one] at this
      linarith
  have hfin : (s i)⁻¹ ^ 2 * scQm A f i i ≤ 4 := by
    have hs2 : 0 ≤ (s i)⁻¹ ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_left hQ hs2
    nlinarith
  calc Real.sqrt ((s i)⁻¹ ^ 2 * scQm A f i i) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hfin
    _ = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
