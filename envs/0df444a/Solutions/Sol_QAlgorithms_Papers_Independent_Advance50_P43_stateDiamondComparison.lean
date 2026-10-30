-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P43.stateDiamondComparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:39:59.023797+00:00
-- url     : https://prove2.me/submissions/54077fd8-4d30-4e84-99a1-520e2fcb8f7a

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P43
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45
  (holevoCapacity resourceCapacity standardEbit)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer diamond)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst privateCapacity)

open QAlgorithms.Papers.Independent.Information100.P22 (quantumCapacity)

open QAlgorithms.Papers.Independent.Dependency50.P23 (ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

variable {A B C Q : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype Q]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq Q]

end QAlgorithms.Papers.Independent.Advance50.P43

open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace
lemma g55bq_sqrt_sq {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
    cfc Real.sqrt (Q * Q) = Q := by
  have hsa : IsSelfAdjoint Q := hQ.1.isSelfAdjoint
  have h1 : Q * Q = cfc (fun t : ℝ => t * t) Q := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) Q, cfc_id' ℝ Q]
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  have : 0 ≤ t := spectrum_nonneg_of_nonneg hnn ht
  simp only [Function.comp, id]
  exact Real.sqrt_mul_self this

lemma g55bq_sqrt_psd {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) :
    (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma g55bq_sqrt_mul_self {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc Real.sqrt (Xᴴ * X) * cfc Real.sqrt (Xᴴ * X) = Xᴴ * X := by
  have hnn : (0 : Matrix n n ℂ) ≤ Xᴴ * X :=
    Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self X)
  rw [← cfc_mul Real.sqrt Real.sqrt (Xᴴ * X)]
  conv_rhs => rw [← cfc_id ℝ (Xᴴ * X)]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma g55bq_polar {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    ∃ W : Matrix n n ℂ, Wᴴ * W = 1 ∧ X = W * cfc Real.sqrt (Xᴴ * X) := by
  set P := cfc Real.sqrt (Xᴴ * X) with hPdef
  have hP : P.PosSemidef := g55bq_sqrt_psd _
  have hPP : P * P = Xᴴ * X := g55bq_sqrt_mul_self X
  let a : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin P
  let b : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin X
  have hinner : ∀ v, ⟪a v, a v⟫_ℂ = ⟪b v, b v⟫_ℂ := by
    intro v
    simp only [a, b, Matrix.toEuclideanLin_apply, EuclideanSpace.inner_toLp_toLp]
    rw [dotProduct_comm, dotProduct_comm (X *ᵥ _)]
    rw [Matrix.star_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP.1.eq, hPP]
  have hnorm : ∀ v, ‖a v‖ = ‖b v‖ := by
    intro v
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), @norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ,
      hinner]
  have hker : LinearMap.ker a ≤ LinearMap.ker b := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← norm_eq_zero, ← hnorm, hv, norm_zero]
  let L0 : LinearMap.range a →ₗ[ℂ] EuclideanSpace ℂ n :=
    (LinearMap.ker a).liftQ b hker ∘ₗ a.quotKerEquivRange.symm.toLinearMap
  have hL0 : ∀ v, L0 ⟨a v, LinearMap.mem_range_self a v⟩ = b v := by
    intro v
    simp only [L0, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let L : LinearMap.range a →ₗᵢ[ℂ] EuclideanSpace ℂ n :=
    { toLinearMap := L0
      norm_map' := by
        rintro ⟨s, v, rfl⟩
        rw [hL0, ← hnorm]
        rfl }
  let E := L.extend
  have hE : ∀ v, E (a v) = b v := by
    intro v
    have := L.extend_apply ⟨a v, LinearMap.mem_range_self a v⟩
    rw [this]
    exact hL0 v
  let W : Matrix n n ℂ := fun i j => (E (EuclideanSpace.single j 1)) i
  have hWv : ∀ v : EuclideanSpace ℂ n, W *ᵥ (WithLp.ofLp v) = WithLp.ofLp (E v) := by
    intro v
    have hv : v = ∑ j, v j • EuclideanSpace.single j (1 : ℂ) := by
      ext i; simp [EuclideanSpace.single_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    ext i
    simp [Matrix.mulVec, dotProduct, W, map_sum, map_smul, mul_comm]
  refine ⟨W, ?_, ?_⟩
  · ext i j
    have := E.inner_map_map (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rw [dotProduct] at this
    simp only [Pi.star_apply] at this
    rw [show (∑ k, star (W k i) * W k j) = ∑ k, (E (EuclideanSpace.single j 1)) k *
      star ((E (EuclideanSpace.single i 1)) k) from Finset.sum_congr rfl (fun k _ => mul_comm _ _)]
    rw [this]
    simp [dotProduct, Pi.single_apply, eq_comm]
  · ext i j
    have h1 := congrFun (hWv (WithLp.toLp 2 (fun k => P k j))) i
    have h2 := hE (EuclideanSpace.single j 1)
    have h3 : a (EuclideanSpace.single j 1) = WithLp.toLp 2 (fun k => P k j) := by
      ext k; simp [a, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
    rw [h3] at h2
    rw [h2] at h1
    simp only [Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct] at h1
    rw [h1]
    simp [b, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]

namespace G55BF

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Frobenius quadratic form. -/
noncomputable def fq (P : Matrix n n ℂ) : ℝ := (Pᴴ * P).trace.re

lemma fq_nonneg (P : Matrix n n ℂ) : 0 ≤ fq P := by
  have := (Matrix.posSemidef_conjTranspose_mul_self P).trace_nonneg
  exact (Complex.nonneg_iff.mp this).1

lemma re_tr_swap (P Q : Matrix n n ℂ) : (Qᴴ * P).trace.re = (Pᴴ * Q).trace.re := by
  have : (Qᴴ * P).trace = star ((Pᴴ * Q).trace) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [this]; simp

lemma cs (P Q : Matrix n n ℂ) : (Pᴴ * Q).trace.re ≤ Real.sqrt (fq P) * Real.sqrt (fq Q) := by
  have hq : ∀ t : ℝ, 0 ≤ fq Q * (t * t) + (-2 * (Pᴴ * Q).trace.re) * t + fq P := by
    intro t
    have h := fq_nonneg (P - (t : ℂ) • Q)
    unfold fq at h ⊢
    have e : (P - (t : ℂ) • Q)ᴴ * (P - (t : ℂ) • Q) =
        Pᴴ * P - (t : ℂ) • (Pᴴ * Q) - (t : ℂ) • (Qᴴ * P) + ((t : ℂ) * t) • (Qᴴ * Q) := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Complex.star_def,
        Complex.conj_ofReal, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul]
      module
    rw [e] at h
    simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Complex.sub_re, Complex.add_re,
      smul_eq_mul, Complex.re_ofReal_mul, ← Complex.ofReal_mul] at h
    rw [re_tr_swap P Q] at h
    nlinarith [h]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have h2 : ((Pᴴ * Q).trace.re) ^ 2 ≤ fq P * fq Q := by nlinarith
  calc (Pᴴ * Q).trace.re ≤ |(Pᴴ * Q).trace.re| := le_abs_self _
    _ = Real.sqrt (((Pᴴ * Q).trace.re) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (fq P * fq Q) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (fq P) * Real.sqrt (fq Q) := Real.sqrt_mul (fq_nonneg P) _

/-- contraction: if 1 - Z*Z is PSD then fq (Z * C) ≤ fq C. -/
lemma fq_contr {Z : Matrix n n ℂ} (hZ : Z.IsHermitian) (h : (1 - Z * Z).PosSemidef)
    (C : Matrix n n ℂ) : fq (Z * C) ≤ fq C := by
  have hp := h.conjTranspose_mul_mul_same C
  have := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  unfold fq
  rw [Matrix.conjTranspose_mul, hZ.eq]
  have e : Cᴴ * (1 - Z * Z) * C = Cᴴ * C - Cᴴ * Z * (Z * C) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e, Matrix.trace_sub, Complex.sub_re] at this
  simp only [Matrix.mul_assoc] at this ⊢
  linarith

lemma core (X Y Z : Matrix n n ℂ) (hZ : Z.IsHermitian) (h : (1 - Z * Z).PosSemidef) :
    (Z * (X * Xᴴ - Y * Yᴴ)).trace.re ≤ Real.sqrt (fq (X + Y)) * Real.sqrt (fq (X - Y)) := by
  set u := X + Y; set v := X - Y
  have e : X * Xᴴ - Y * Yᴴ = (1 / 2 : ℂ) • (v * uᴴ + u * vᴴ) := by
    simp only [u, v, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.add_mul, Matrix.sub_mul,
      Matrix.mul_add, Matrix.mul_sub, smul_add, smul_sub]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [e, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add]
  have t1 : (Z * (v * uᴴ)).trace = (uᴴ * (Z * v)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have t2 : (Z * (u * vᴴ)).trace = (vᴴ * (Z * u)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [t1, t2]
  have c1 := cs u (Z * v)
  have c2 := cs v (Z * u)
  have k1 := Real.sqrt_le_sqrt (fq_contr hZ h v)
  have k2 := Real.sqrt_le_sqrt (fq_contr hZ h u)
  have s1 := Real.sqrt_nonneg (fq u)
  have s2 := Real.sqrt_nonneg (fq v)
  rw [smul_eq_mul]
  have : ((1 / 2 : ℂ) * ((uᴴ * (Z * v)).trace + (vᴴ * (Z * u)).trace)).re =
      (1 / 2) * ((uᴴ * (Z * v)).trace.re + (vᴴ * (Z * u)).trace.re) := by
    simp [Complex.mul_re]
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left k1 s1, mul_le_mul_of_nonneg_left k2 s2]

lemma sqrt_mul_sqrt {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) : cfc Real.sqrt Q * cfc Real.sqrt Q = Q := by
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [← cfc_mul Real.sqrt Real.sqrt Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma fq_tr {X : Matrix n n ℂ} : fq X = (X * Xᴴ).trace.re := by
  unfold fq; rw [Matrix.trace_mul_comm]

lemma fq_add (X Y : Matrix n n ℂ) : fq (X + Y) = fq X + fq Y + 2 * (Xᴴ * Y).trace.re := by
  unfold fq
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add,
    Matrix.trace_add, Matrix.trace_add, Complex.add_re, Complex.add_re, Complex.add_re, re_tr_swap Y X]
  ring

lemma fq_sub (X Y : Matrix n n ℂ) : fq (X - Y) = fq X + fq Y - 2 * (Xᴴ * Y).trace.re := by
  have := fq_add X (-Y)
  rw [← sub_eq_add_neg] at this
  rw [this]
  unfold fq
  simp [Matrix.trace_neg]
  ring

lemma fvdg {ρ σ Z : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (tρ : ρ.trace = 1)
    (tσ : σ.trace = 1) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hZ : Z.IsHermitian)
    (h : (1 - Z * Z).PosSemidef) :
    (Z * ((p : ℂ) • ρ - (q : ℂ) • σ)).trace.re ≤
      Real.sqrt (p ^ 2 + 2 * (1 - 2 * ((cfc Real.sqrt (cfc Real.sqrt ρ * σ * cfc Real.sqrt ρ)).trace.re) ^ 2)
        * p * q + q ^ 2) := by
  set Rρ := cfc Real.sqrt ρ with hRρ
  set Rσ := cfc Real.sqrt σ with hRσ
  have hRρH : Rρᴴ = Rρ := (g55bq_sqrt_psd ρ).1.eq
  have hRσH : Rσᴴ = Rσ := (g55bq_sqrt_psd σ).1.eq
  have hRρ2 : Rρ * Rρ = ρ := sqrt_mul_sqrt hρ
  have hRσ2 : Rσ * Rσ = σ := sqrt_mul_sqrt hσ
  obtain ⟨W, hW, hpol⟩ := g55bq_polar (Rσ * Rρ)
  have hKK : (Rσ * Rρ)ᴴ * (Rσ * Rρ) = Rρ * σ * Rρ := by
    rw [Matrix.conjTranspose_mul, hRρH, hRσH, Matrix.mul_assoc, ← Matrix.mul_assoc Rσ, hRσ2,
      Matrix.mul_assoc]
  rw [hKK] at hpol
  set Ab := cfc Real.sqrt (Rρ * σ * Rρ) with hAb
  have hAbH : Abᴴ = Ab := (g55bq_sqrt_psd _).1.eq
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  set X : Matrix n n ℂ := ((Real.sqrt p : ℝ) : ℂ) • Rρ with hX
  set Y : Matrix n n ℂ := ((Real.sqrt q : ℝ) : ℂ) • (Rσ * W) with hY
  have hsp : ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt p : ℝ) : ℂ) = p := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp]
  have hsq : ((Real.sqrt q : ℝ) : ℂ) * ((Real.sqrt q : ℝ) : ℂ) = q := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hq]
  have hXX : X * Xᴴ = (p : ℂ) • ρ := by
    rw [hX, Matrix.conjTranspose_smul, hRρH, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hRρ2]
    simp [Complex.star_def, hsp]
  have hYY : Y * Yᴴ = (q : ℂ) • σ := by
    rw [hY, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.conjTranspose_mul, hRσH, Matrix.mul_assoc, ← Matrix.mul_assoc W, hW', Matrix.one_mul, hRσ2]
    simp [Complex.star_def, hsq]
  have fX : fq X = p := by
    rw [fq_tr, hXX, Matrix.trace_smul, tρ]; simp
  have fY : fq Y = q := by
    rw [fq_tr, hYY, Matrix.trace_smul, tσ]; simp
  set F := (Ab.trace).re with hF
  have hXY : (Xᴴ * Y).trace.re = Real.sqrt p * Real.sqrt q * F := by
    have hK : Rρ * Rσ = Ab * Wᴴ := by
      have := congrArg Matrix.conjTranspose hpol
      rw [Matrix.conjTranspose_mul, hRρH, hRσH, Matrix.conjTranspose_mul, hAbH] at this
      exact this
    rw [hX, hY, Matrix.conjTranspose_smul, hRρH, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← Matrix.mul_assoc, hK, Matrix.mul_assoc, hW, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
    simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.re_ofReal_mul, hF]
  have hcore := core X Y Z hZ h
  rw [hXX, hYY] at hcore
  refine hcore.trans (le_of_eq ?_)
  rw [← Real.sqrt_mul (fq_nonneg _), fq_add, fq_sub, fX, fY, hXY]
  congr 1
  have e1 : (Real.sqrt p * Real.sqrt q) ^ 2 = p * q := by
    rw [mul_pow, Real.sq_sqrt hp, Real.sq_sqrt hq]
  have : (p + q + 2 * (Real.sqrt p * Real.sqrt q * F)) * (p + q - 2 * (Real.sqrt p * Real.sqrt q * F)) =
      (p + q) ^ 2 - 4 * (Real.sqrt p * Real.sqrt q) ^ 2 * F ^ 2 := by ring
  rw [this, e1]; ring

lemma sum_psd {ι : Type*} (s : Finset ι) (A : ι → Matrix n n ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

lemma one_sub_sq {Z : Matrix n n ℂ} (hZ : Z.IsHermitian) (h1 : (1 - Z).PosSemidef)
    (h2 : (1 + Z).PosSemidef) : (1 - Z * Z).PosSemidef := by
  have hsa : IsSelfAdjoint Z := hZ
  have hle : ∀ t ∈ spectrum ℝ Z, t ≤ 1 := by
    have : Z ≤ algebraMap ℝ (Matrix n n ℂ) 1 := by
      rw [map_one, ← sub_nonneg, Matrix.nonneg_iff_posSemidef]; exact h1
    exact (le_algebraMap_iff_spectrum_le).mp this
  have hge : ∀ t ∈ spectrum ℝ Z, -1 ≤ t := by
    have : algebraMap ℝ (Matrix n n ℂ) (-1) ≤ Z := by
      rw [map_neg, map_one, ← sub_nonneg, sub_neg_eq_add, add_comm, Matrix.nonneg_iff_posSemidef]
      exact h2
    exact (algebraMap_le_iff_le_spectrum).mp this
  have e : 1 - Z * Z = cfc (fun t : ℝ => 1 - t * t) Z := by
    rw [cfc_sub (fun _ => (1 : ℝ)) (fun t : ℝ => t * t) Z, cfc_const_one ℝ Z,
      cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) Z, cfc_id' ℝ Z]
  rw [e, ← Matrix.nonneg_iff_posSemidef]
  apply cfc_nonneg
  intro t ht
  nlinarith [hle t ht, hge t ht]

lemma povm_contr {M : ℕ} (D : Fin M → Matrix n n ℂ) (hD : ∀ k, (D k).PosSemidef)
    (hs : ∑ k, D k = 1) (i j : Fin M) :
    (D i - D j).IsHermitian ∧ (1 - (D i - D j) * (D i - D j)).PosSemidef := by
  have hH : (D i - D j).IsHermitian := (hD i).1.sub (hD j).1
  refine ⟨hH, one_sub_sq hH ?_ ?_⟩
  · have : 1 - (D i - D j) = (∑ k ∈ Finset.univ.erase i, D k) + D j := by
      rw [← hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; abel
    rw [this]; exact (sum_psd _ _ hD).add (hD j)
  · have : 1 + (D i - D j) = (∑ k ∈ Finset.univ.erase j, D k) + D i := by
      rw [← hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]; abel
    rw [this]; exact (sum_psd _ _ hD).add (hD i)

lemma pair_sum {M : ℕ} (g : Fin M → Fin M → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (g i j + g j i) =
      ∑ i, ∑ j, g i j - ∑ i, g i i := by
  simp only [Finset.sum_filter]
  have h1 : ∑ i : Fin M, ∑ j : Fin M, (if i < j then g i j + g j i else 0) =
      ∑ i : Fin M, ∑ j : Fin M, (if i < j then g i j else 0) +
        ∑ i : Fin M, ∑ j : Fin M, (if j < i then g i j else 0) := by
    rw [Finset.sum_comm (f := fun i j => if j < i then g i j else 0), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [h1, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (s := Finset.univ) (a := i) (fun j => g i j) (Finset.mem_univ i)]
  simp only [lt_irrefl, if_false, add_zero]
  have : ∀ j ∈ Finset.univ.erase i, ((if i < j then g i j else 0) + if j < i then g i j else 0) = g i j := by
    intro j hj
    have hne : j ≠ i := Finset.ne_of_mem_erase hj
    rcases lt_or_gt_of_ne hne with h | h
    · simp [h, not_lt.mpr h.le]
    · simp [h, not_lt.mpr h.le]
  rw [Finset.sum_congr rfl this]
  ring

lemma tr_psd_mul {P Q : Matrix n n ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace.re := by
  have hR : (cfc Real.sqrt Q)ᴴ = cfc Real.sqrt Q := (g55bq_sqrt_psd Q).1.eq
  have h := (hP.conjTranspose_mul_mul_same (cfc Real.sqrt Q)).trace_nonneg
  rw [hR, Matrix.trace_mul_comm, ← Matrix.mul_assoc, sqrt_mul_sqrt hQ, Matrix.trace_mul_comm] at h
  exact (Complex.nonneg_iff.mp h).1

lemma povm_pair {M : ℕ} (D : Fin M → Matrix n n ℂ) (hD : ∀ k, (D k).PosSemidef)
    (hs : ∑ k, D k = 1) {i j : Fin M} (hij : i ≠ j) : (1 - (D i + D j)).PosSemidef := by
  have : 1 - (D i + D j) = ∑ k ∈ (Finset.univ.erase i).erase j, D k := by
    rw [← hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
    abel
  rw [this]; exact sum_psd _ _ hD

end G55BF
section G53D
open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace
lemma g55b_sqrt_sq {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
    cfc Real.sqrt (Q * Q) = Q := by
  have hsa : IsSelfAdjoint Q := hQ.1.isSelfAdjoint
  have h1 : Q * Q = cfc (fun t : ℝ => t * t) Q := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) Q, cfc_id' ℝ Q]
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  have : 0 ≤ t := spectrum_nonneg_of_nonneg hnn ht
  simp only [Function.comp, id]
  exact Real.sqrt_mul_self this

lemma g55b_sqrt_psd {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) :
    (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma g55b_sqrt_mul_self {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc Real.sqrt (Xᴴ * X) * cfc Real.sqrt (Xᴴ * X) = Xᴴ * X := by
  have hnn : (0 : Matrix n n ℂ) ≤ Xᴴ * X :=
    Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self X)
  rw [← cfc_mul Real.sqrt Real.sqrt (Xᴴ * X)]
  conv_rhs => rw [← cfc_id ℝ (Xᴴ * X)]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma g55b_polar {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    ∃ W : Matrix n n ℂ, Wᴴ * W = 1 ∧ X = W * cfc Real.sqrt (Xᴴ * X) := by
  set P := cfc Real.sqrt (Xᴴ * X) with hPdef
  have hP : P.PosSemidef := g55b_sqrt_psd _
  have hPP : P * P = Xᴴ * X := g55b_sqrt_mul_self X
  let a : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin P
  let b : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n := Matrix.toEuclideanLin X
  have hinner : ∀ v, ⟪a v, a v⟫_ℂ = ⟪b v, b v⟫_ℂ := by
    intro v
    simp only [a, b, Matrix.toEuclideanLin_apply, EuclideanSpace.inner_toLp_toLp]
    rw [dotProduct_comm, dotProduct_comm (X *ᵥ _)]
    rw [Matrix.star_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP.1.eq, hPP]
  have hnorm : ∀ v, ‖a v‖ = ‖b v‖ := by
    intro v
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), @norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ,
      hinner]
  have hker : LinearMap.ker a ≤ LinearMap.ker b := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← norm_eq_zero, ← hnorm, hv, norm_zero]
  let L0 : LinearMap.range a →ₗ[ℂ] EuclideanSpace ℂ n :=
    (LinearMap.ker a).liftQ b hker ∘ₗ a.quotKerEquivRange.symm.toLinearMap
  have hL0 : ∀ v, L0 ⟨a v, LinearMap.mem_range_self a v⟩ = b v := by
    intro v
    simp only [L0, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let L : LinearMap.range a →ₗᵢ[ℂ] EuclideanSpace ℂ n :=
    { toLinearMap := L0
      norm_map' := by
        rintro ⟨s, v, rfl⟩
        rw [hL0, ← hnorm]
        rfl }
  let E := L.extend
  have hE : ∀ v, E (a v) = b v := by
    intro v
    have := L.extend_apply ⟨a v, LinearMap.mem_range_self a v⟩
    rw [this]
    exact hL0 v
  let W : Matrix n n ℂ := fun i j => (E (EuclideanSpace.single j 1)) i
  have hWv : ∀ v : EuclideanSpace ℂ n, W *ᵥ (WithLp.ofLp v) = WithLp.ofLp (E v) := by
    intro v
    have hv : v = ∑ j, v j • EuclideanSpace.single j (1 : ℂ) := by
      ext i; simp [EuclideanSpace.single_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    ext i
    simp [Matrix.mulVec, dotProduct, W, map_sum, map_smul, mul_comm]
  refine ⟨W, ?_, ?_⟩
  · ext i j
    have := E.inner_map_map (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rw [dotProduct] at this
    simp only [Pi.star_apply] at this
    rw [show (∑ k, star (W k i) * W k j) = ∑ k, (E (EuclideanSpace.single j 1)) k *
      star ((E (EuclideanSpace.single i 1)) k) from Finset.sum_congr rfl (fun k _ => mul_comm _ _)]
    rw [this]
    simp [dotProduct, Pi.single_apply, eq_comm]
  · ext i j
    have h1 := congrFun (hWv (WithLp.toLp 2 (fun k => P k j))) i
    have h2 := hE (EuclideanSpace.single j 1)
    have h3 : a (EuclideanSpace.single j 1) = WithLp.toLp 2 (fun k => P k j) := by
      ext k; simp [a, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
    rw [h3] at h2
    rw [h2] at h1
    simp only [Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct] at h1
    rw [h1]
    simp [b, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]



end G53D
open QAlgorithms
lemma g55b_psd_trace {n : Type*} [Fintype n] {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    P.trace = ((P.trace.re : ℝ) : ℂ) := by
  have h := hP.trace_nonneg
  rw [Complex.nonneg_iff] at h
  apply Complex.ext <;> simp [← h.2]

lemma g55b_tn_psd {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    (traceNorm P : ℂ) = P.trace := by
  unfold traceNorm
  rw [hP.1.eq, g55b_sqrt_sq hP, ← g55b_psd_trace hP]

/-- polar: B = W P with W unitary, and traces. -/
lemma g55b_polar_tr {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) :
    ∃ W : Matrix n n ℂ, Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ (Wᴴ * B).trace = (traceNorm B : ℂ) ∧
      (Bᴴ * W).trace = (traceNorm B : ℂ) ∧ traceNorm Bᴴ = traceNorm B := by
  obtain ⟨W, hW, hB⟩ := g55b_polar B
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  set P := cfc Real.sqrt (Bᴴ * B) with hPdef
  have hP : P.PosSemidef := g55b_sqrt_psd _
  have hPh : Pᴴ = P := hP.1.eq
  have htn : (traceNorm B : ℂ) = P.trace := by
    unfold traceNorm; rw [← hPdef, ← g55b_psd_trace hP]
  have h1 : (Wᴴ * B).trace = (traceNorm B : ℂ) := by
    rw [htn, hB, ← Matrix.mul_assoc, hW, Matrix.one_mul]
  refine ⟨W, hW, hW', h1, ?_, ?_⟩
  · have : (Bᴴ * W).trace = star ((Wᴴ * B).trace) := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [this, h1]; simp
  · have hQ : (W * P * Wᴴ).PosSemidef := by
      simpa [Matrix.conjTranspose_conjTranspose] using hP.conjTranspose_mul_mul_same Wᴴ
    have hsq : (Bᴴ)ᴴ * Bᴴ = (W * P * Wᴴ) * (W * P * Wᴴ) := by
      rw [Matrix.conjTranspose_conjTranspose]
      conv_lhs => rw [hB]
      rw [Matrix.conjTranspose_mul, hPh]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul]
    have : traceNorm Bᴴ = (W * P * Wᴴ).trace.re := by
      unfold traceNorm; rw [hsq, g55b_sqrt_sq hQ]
    rw [this, Matrix.trace_mul_cycle, hW, Matrix.one_mul]
    have := congrArg Complex.re htn
    simpa using this.symm

namespace S64FC
open G55BF Matrix
open scoped Kronecker

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma tn_zero : traceNorm (0 : Matrix n n ℂ) = 0 := by unfold traceNorm; simp

lemma tn_nonneg (M : Matrix n n ℂ) : 0 ≤ traceNorm M := by
  unfold traceNorm; exact (Complex.nonneg_iff.1 (g55b_sqrt_psd _).trace_nonneg).1

lemma re_tr_le_tn (V M : Matrix n n ℂ) (hV : V * Vᴴ = 1) : (V * M).trace.re ≤ traceNorm M := by
  obtain ⟨W, hW, hM⟩ := g55b_polar M
  set P := cfc Real.sqrt (Mᴴ * M) with hP
  have hPp : P.PosSemidef := g55b_sqrt_psd _
  set s := cfc Real.sqrt P with hs
  have hsh : sᴴ = s := (g55b_sqrt_psd P).1.eq
  have hss : s * s = P := G55BF.sqrt_mul_sqrt hPp
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  have e : (V * M).trace = ((Wᴴ * Vᴴ * s)ᴴ * s).trace := by
    rw [show (Wᴴ * Vᴴ * s)ᴴ * s = s * (V * W * s) by
      simp [Matrix.conjTranspose_mul, hsh, Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm s, hM, ← hss]; simp only [Matrix.mul_assoc]
  have c := cs (Wᴴ * Vᴴ * s) s
  have f1 : fq (Wᴴ * Vᴴ * s) = P.trace.re := by
    unfold fq
    rw [show (Wᴴ * Vᴴ * s)ᴴ * (Wᴴ * Vᴴ * s) = s * (V * (W * Wᴴ) * Vᴴ) * s by
      simp [Matrix.conjTranspose_mul, hsh, Matrix.mul_assoc]]
    rw [hW', Matrix.mul_one, hV, Matrix.mul_one, hss]
  have f2 : fq s = P.trace.re := by unfold fq; rw [hsh, hss]
  rw [e]
  rw [f1, f2] at c
  have hp0 : 0 ≤ P.trace.re := (Complex.nonneg_iff.1 hPp.trace_nonneg).1
  rw [Real.mul_self_sqrt hp0] at c
  exact c

lemma tn_add_le (A B : Matrix n n ℂ) : traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  obtain ⟨W, hW, hW', htr, -, -⟩ := g55b_polar_tr (A + B)
  have h : traceNorm (A + B) = (Wᴴ * (A + B)).trace.re := by rw [htr]; simp
  have hu : Wᴴ * (Wᴴ)ᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hW
  rw [h, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  exact add_le_add (re_tr_le_tn _ _ hu) (re_tr_le_tn _ _ hu)

lemma tn_smul_le (c : ℂ) (A : Matrix n n ℂ) : traceNorm (c • A) ≤ ‖c‖ * traceNorm A := by
  by_cases hc : c = 0
  · subst hc; simp [tn_zero]
  obtain ⟨W, hW, hW', htr, -, -⟩ := g55b_polar_tr (c • A)
  have hn : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hc)
  set u : ℂ := c / (‖c‖ : ℂ)
  have hu1 : u * star u = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_div, Complex.normSq_ofReal,
      ← Complex.sq_norm]
    have : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hc)
    field_simp; push_cast; ring
  have hcu : c = (‖c‖ : ℂ) * u := by simp only [u]; field_simp
  have h : traceNorm (c • A) = ‖c‖ * ((u • Wᴴ) * A).trace.re := by
    have h1 : traceNorm (c • A) = (Wᴴ * (c • A)).trace.re := by rw [htr]; simp
    have h2 : Wᴴ * (c • A) = (‖c‖ : ℂ) • ((u • Wᴴ) * A) := by
      rw [Matrix.smul_mul, smul_smul, ← hcu, Matrix.mul_smul]
    rw [h1, h2, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hV : (u • Wᴴ) * (u • Wᴴ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hW, hu1, one_smul]
  rw [h]
  exact mul_le_mul_of_nonneg_left (re_tr_le_tn _ _ hV) (norm_nonneg _)

lemma tn_sum_le {ι : Type*} (s : Finset ι) (f : ι → Matrix n n ℂ) :
    traceNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, traceNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tn_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (tn_add_le _ _).trans (add_le_add le_rfl ih)

lemma tn_traceRight_le {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix (n × m) (n × m) ℂ) :
    traceNorm (traceRight M) ≤ traceNorm M := by
  obtain ⟨W, hW, hW', htr, -, -⟩ := g55b_polar_tr (traceRight M)
  have h : traceNorm (traceRight M) = (Wᴴ * traceRight M).trace.re := by rw [htr]; simp
  set V : Matrix (n × m) (n × m) ℂ := Wᴴ ⊗ₖ (1 : Matrix m m ℂ)
  have hV : V * Vᴴ = 1 := by
    simp only [V, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one]
    rw [← Matrix.mul_kronecker_mul, hW, Matrix.mul_one, Matrix.one_kronecker_one]
  have e : (V * M).trace = (Wᴴ * traceRight M).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, V, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.one_apply, traceRight, Matrix.of_apply,
      Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    exact Finset.sum_comm
  rw [h, ← e]
  exact re_tr_le_tn V M hV

end S64FC
namespace S64FC2
open G55BF Matrix S64FC
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma dot_star_real (v : n → ℂ) :
    star v ⬝ᵥ v = (((star v ⬝ᵥ v).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im, dotProduct, Complex.im_sum]
    apply Finset.sum_eq_zero
    intro i _
    simp [Complex.mul_im]; ring

lemma dot_star_re_nonneg (v : n → ℂ) : 0 ≤ (star v ⬝ᵥ v).re := by
  have := dotProduct_star_self_nonneg v
  exact (Complex.nonneg_iff.mp this).1

end S64FC2
namespace S64T6
open G55BF Matrix S64FC S64FC2

variable {N : Type*} [Fintype N] [DecidableEq N]

lemma rank_one_dec (X : Matrix N N ℂ) : ∃ a b : N → N → ℂ,
    X = ∑ j, vecMulVec (a j) (star (b j)) ∧ ∑ j, (star (a j) ⬝ᵥ a j).re = traceNorm X ∧
    ∑ j, (star (b j) ⬝ᵥ b j).re = traceNorm X := by
  obtain ⟨W, hW, hX⟩ := g55b_polar X
  set P := cfc Real.sqrt (Xᴴ * X) with hP
  have hPp : P.PosSemidef := g55b_sqrt_psd _
  set sP := cfc Real.sqrt P with hsPdef
  have hsh : sPᴴ = sP := (g55b_sqrt_psd P).1.eq
  have hss : sP * sP = P := G55BF.sqrt_mul_sqrt hPp
  set A := W * sP with hA
  refine ⟨fun j i => A i j, fun j i => sP i j, ?_, ?_, ?_⟩
  · ext x y
    rw [Matrix.sum_apply]
    simp only [vecMulVec_apply, Pi.star_apply]
    have : ∀ j, star (sP y j) = sP j y := by
      intro j
      have := congrFun (congrFun hsh j) y
      rwa [Matrix.conjTranspose_apply] at this
    simp only [this]
    rw [hX, ← hss, ← Matrix.mul_assoc, Matrix.mul_apply]
  · have hna : ∀ j, (star (fun i => A i j) ⬝ᵥ (fun i => A i j)).re = (P j j).re := by
      intro j
      have : star (fun i => A i j) ⬝ᵥ (fun i => A i j) = (Aᴴ * A) j j := by
        simp [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [this, hA, Matrix.conjTranspose_mul, hsh,
        show sP * Wᴴ * (W * sP) = sP * (Wᴴ * W) * sP by simp [Matrix.mul_assoc], hW,
        Matrix.mul_one, hss]
    simp only [hna]
    unfold traceNorm
    rw [← hP, Matrix.trace, Complex.re_sum]; rfl
  · have hnb : ∀ j, (star (fun i => sP i j) ⬝ᵥ (fun i => sP i j)).re = (P j j).re := by
      intro j
      have : star (fun i => sP i j) ⬝ᵥ (fun i => sP i j) = (sPᴴ * sP) j j := by
        simp [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [this, hsh, hss]
    simp only [hnb]
    unfold traceNorm
    rw [← hP, Matrix.trace, Complex.re_sum]; rfl

lemma tn_rank1 (x y : N → ℂ) :
    traceNorm (vecMulVec x (star y)) ≤ ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) / 2 := by
  obtain ⟨W, hW, hW', htr, -, -⟩ := g55b_polar_tr (vecMulVec x (star y))
  have h : traceNorm (vecMulVec x (star y)) = (star y ⬝ᵥ (Wᴴ *ᵥ x)).re := by
    have : (Wᴴ * vecMulVec x (star y)).trace = star y ⬝ᵥ (Wᴴ *ᵥ x) := by
      rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
    rw [← this, htr]; simp
  set u := Wᴴ *ᵥ x
  have hu : star u ⬝ᵥ u = star x ⬝ᵥ x := by
    simp only [u]
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.conjTranspose_conjTranspose, hW', Matrix.one_mulVec]
  have h0 := dot_star_re_nonneg (y - u)
  have e : (star (y - u) ⬝ᵥ (y - u)).re =
      (star y ⬝ᵥ y).re + (star u ⬝ᵥ u).re - 2 * (star y ⬝ᵥ u).re := by
    have hs : (star u ⬝ᵥ y).re = (star y ⬝ᵥ u).re := by
      have : star u ⬝ᵥ y = star (star y ⬝ᵥ u) := by
        simp [dotProduct, mul_comm, star_sum]
      rw [this]; simp
    simp only [star_sub, sub_dotProduct, dotProduct_sub, Complex.sub_re, hs]
    ring
  rw [h]
  rw [e, hu] at h0
  linarith

end S64T6

open scoped Matrix ComplexOrder MatrixOrder
open QAlgorithms Matrix G55BF S64FC S64FC2 S64T6

section s14
variable {M N : Type} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

lemma s14_contr (V W : Matrix M N ℂ)
    (hV : ∀ x : N → ℂ, (star (V *ᵥ x) ⬝ᵥ (V *ᵥ x)).re ≤ (star x ⬝ᵥ x).re)
    (hW : ∀ x : N → ℂ, (star (W *ᵥ x) ⬝ᵥ (W *ᵥ x)).re ≤ (star x ⬝ᵥ x).re)
    (H : Matrix N N ℂ) : traceNorm (V * H * Wᴴ) ≤ traceNorm H := by
  obtain ⟨a, b, hX, ha, hb⟩ := rank_one_dec H
  have e : V * H * Wᴴ = ∑ j, vecMulVec (V *ᵥ a j) (star (W *ᵥ b j)) := by
    rw [hX, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]
  rw [e]
  refine (tn_sum_le _ _).trans ?_
  calc ∑ j, traceNorm (vecMulVec (V *ᵥ a j) (star (W *ᵥ b j)))
      ≤ ∑ j, ((star (V *ᵥ a j) ⬝ᵥ (V *ᵥ a j)).re + (star (W *ᵥ b j) ⬝ᵥ (W *ᵥ b j)).re) / 2 :=
        Finset.sum_le_sum fun j _ => tn_rank1 _ _
    _ ≤ ∑ j, ((star (a j) ⬝ᵥ a j).re + (star (b j) ⬝ᵥ b j).re) / 2 :=
        Finset.sum_le_sum fun j _ => by linarith [hV (a j), hW (b j)]
    _ = traceNorm H := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, ha, hb]; ring

lemma s14_polar (x y : N → ℂ) :
    vecMulVec x (star y) = (1/4 : ℂ) • (vecMulVec (x + y) (star (x + y)) -
      vecMulVec (x - y) (star (x - y)) + Complex.I • vecMulVec (x + Complex.I • y) (star (x + Complex.I • y)) -
      Complex.I • vecMulVec (x - Complex.I • y) (star (x - Complex.I • y))) := by
  ext i j
  simp only [vecMulVec_apply, Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, star_add, star_sub, star_mul',
    Complex.star_def, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]; ring

lemma s14_polar_norm (x y : N → ℂ) :
    (star (x + y) ⬝ᵥ (x + y)).re + (star (x - y) ⬝ᵥ (x - y)).re +
      (star (x + Complex.I • y) ⬝ᵥ (x + Complex.I • y)).re +
      (star (x - Complex.I • y) ⬝ᵥ (x - Complex.I • y)).re =
      4 * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) := by
  have : star (x + y) ⬝ᵥ (x + y) + star (x - y) ⬝ᵥ (x - y) +
      star (x + Complex.I • y) ⬝ᵥ (x + Complex.I • y) +
      star (x - Complex.I • y) ⬝ᵥ (x - Complex.I • y) = 4 * (star x ⬝ᵥ x + star y ⬝ᵥ y) := by
    simp only [dotProduct, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_add,
      star_sub, star_mul', Complex.star_def, Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]; ring
  have h2 := congrArg Complex.re this
  simp only [Complex.add_re] at h2
  rw [h2]
  simp [Complex.mul_re]
end s14

section s14b
variable {Q B : Type} [Fintype Q] [DecidableEq Q] [Fintype B] [DecidableEq B]

lemma s14_tn_sub (A C : Matrix B B ℂ) : traceNorm (A - C) ≤ traceNorm A + traceNorm C := by
  rw [sub_eq_add_neg, show -C = (-1 : ℂ) • C by simp]
  refine (tn_add_le _ _).trans ?_
  have := tn_smul_le (-1 : ℂ) C
  simp only [norm_neg, norm_one, one_mul] at this
  linarith

lemma s14_lin (Φ Ψ : Superop Q B) (hΦ : IsChannel Φ) (hΨ : IsChannel Ψ) :
    ∃ L : Matrix Q Q ℂ →ₗ[ℂ] Matrix B B ℂ, ∀ X, L X = Φ X - Ψ X := by
  obtain ⟨m, E, -, hE⟩ := hΦ
  obtain ⟨m', F, -, hF⟩ := hΨ
  refine ⟨{ toFun := fun X => Φ X - Ψ X, map_add' := ?_, map_smul' := ?_ }, fun X => rfl⟩
  · intro X Y
    simp only [hE, hF, krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
    abel
  · intro c X
    simp only [hE, hF, krausApply, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum,
      RingHom.id_apply, smul_sub]

lemma s14_chan_tn (Φ : Superop Q B) (hΦ : IsChannel Φ) (ρ : Matrix Q Q ℂ)
    (hρ : IsDensityMatrix ρ) : traceNorm (Φ ρ) = 1 := by
  obtain ⟨m, E, hK, hE⟩ := hΦ
  have hpsd : (Φ ρ).PosSemidef := by
    rw [hE]
    unfold krausApply
    exact Matrix.posSemidef_sum _ fun j _ => hρ.1.mul_mul_conjTranspose_same (E j)
  have htr : (Φ ρ).trace = 1 := by
    rw [hE]; unfold krausApply
    rw [Matrix.trace_sum]
    have : ∀ j, (E j * ρ * (E j)ᴴ).trace = (ρ * ((E j)ᴴ * E j)).trace := by
      intro j
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
      exact Matrix.trace_mul_comm _ _
    simp only [this, ← Matrix.trace_sum, ← Matrix.mul_sum]
    unfold IsKrausFamily at hK
    rw [hK, Matrix.mul_one, hρ.2]
  have := g55b_tn_psd hpsd
  rw [htr] at this
  exact_mod_cast this

lemma s14_bdd (Φ Ψ : Superop Q B) (hΦ : IsChannel Φ) (hΨ : IsChannel Ψ) (ρ : Matrix Q Q ℂ)
    (hρ : IsDensityMatrix ρ) : traceNorm (Φ ρ - Ψ ρ) ≤ 2 := by
  have := s14_tn_sub (Φ ρ) (Ψ ρ)
  rw [s14_chan_tn Φ hΦ ρ hρ, s14_chan_tn Ψ hΨ ρ hρ] at this
  linarith

def s14_iota (r : Q) : Matrix (Q × B) B ℂ := Matrix.of fun x k => if x.1 = r then (1 : Matrix B B ℂ) x.2 k else 0

lemma s14_iota_norm (r : Q) (x : B → ℂ) :
    (star (s14_iota r *ᵥ x) ⬝ᵥ (s14_iota r *ᵥ x)).re ≤ (star x ⬝ᵥ x).re := by
  have hv : s14_iota r *ᵥ x = fun p : Q × B => if p.1 = r then x p.2 else 0 := by
    funext p
    by_cases h : p.1 = r <;> simp [s14_iota, Matrix.mulVec, dotProduct, h, Matrix.one_apply]
  rw [hv]
  apply le_of_eq
  simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, apply_ite star, star_zero,
    ite_mul, mul_ite, mul_zero, zero_mul, ite_self, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

lemma s14_iotaH_norm (r : Q) (v : Q × B → ℂ) :
    (star ((s14_iota r)ᴴ *ᵥ v) ⬝ᵥ ((s14_iota r)ᴴ *ᵥ v)).re ≤ (star v ⬝ᵥ v).re := by
  have hv : (s14_iota r)ᴴ *ᵥ v = fun k => v (r, k) := by
    funext k
    simp only [s14_iota, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type]
    simp [Matrix.one_apply, apply_ite star]
  rw [hv]
  have hnn : ∀ p : Q × B, 0 ≤ (star (v p) * v p).re := fun p => by
    rw [Complex.star_def, Complex.mul_re]; simp; nlinarith [sq_nonneg (v p).re, sq_nonneg (v p).im]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  rw [Fintype.sum_prod_type (f := fun p => (star (v p) * v p).re)]
  exact Finset.single_le_sum (f := fun p => ∑ k, (star (v (p, k)) * v (p, k)).re)
    (fun p _ => Finset.sum_nonneg fun k _ => hnn (p, k)) (Finset.mem_univ r)


lemma s14_idT_rank1 (T : Matrix Q Q ℂ → Matrix B B ℂ) (a b : Q × Q → ℂ) :
    idTensorSuperop (R := Q) T (vecMulVec a (star b)) =
      ∑ r, ∑ s, (s14_iota r : Matrix (Q × B) B ℂ) *
        (T (vecMulVec (fun i => a (r, i)) (star fun i => b (s, i))) : Matrix B B ℂ) *
        ((s14_iota s)ᴴ : Matrix B (Q × B) ℂ) := by
  ext ⟨p, i⟩ ⟨q, i'⟩
  have hblk : (Matrix.of fun j j' => vecMulVec a (star b) (p, j) (q, j')) =
      vecMulVec (fun i => a (p, i)) (star fun i => b (q, i)) := by
    ext j j'; simp [vecMulVec_apply]
  simp only [idTensorSuperop, Matrix.of_apply, hblk, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, s14_iota]
  simp [Matrix.one_apply, apply_ite star, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma s14_idT_sum (L : Matrix Q Q ℂ →ₗ[ℂ] Matrix B B ℂ) {J : Type} [Fintype J]
    (X : J → Matrix (Q × Q) (Q × Q) ℂ) :
    idTensorSuperop (R := Q) (⇑L) (∑ j, X j) = ∑ j, idTensorSuperop (R := Q) (⇑L) (X j) := by
  ext p q
  have hblk : (Matrix.of fun i i' => (∑ j, X j) (p.1, i) (q.1, i')) =
      ∑ j, Matrix.of fun i i' => X j (p.1, i) (q.1, i') := by
    ext i i'; simp [Matrix.sum_apply]
  simp only [idTensorSuperop, Matrix.of_apply, Matrix.sum_apply]
  rw [← Matrix.sum_apply, ← map_sum, ← hblk]
  simp only [Matrix.sum_apply]

lemma s14_normsplit (a : Q × Q → ℂ) :
    (star a ⬝ᵥ a).re = ∑ r, (star (fun i => a (r, i)) ⬝ᵥ (fun i => a (r, i))).re := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  rw [Fintype.sum_prod_type (f := fun p => (star (a p) * a p).re)]

lemma s14_main (L : Matrix Q Q ℂ →ₗ[ℂ] Matrix B B ℂ) (sd : ℝ)
    (hpure : ∀ w : Q → ℂ, traceNorm (L (vecMulVec w (star w))) ≤ sd * (star w ⬝ᵥ w).re)
    (X : Matrix (Q × Q) (Q × Q) ℂ) :
    traceNorm (idTensorSuperop (R := Q) (⇑L) X) ≤ 2 * Fintype.card Q * sd * traceNorm X := by
  have hsd : 0 ≤ sd ∨ True := Or.inr trivial
  have hr1 : ∀ x y : Q → ℂ, traceNorm (L (vecMulVec x (star y))) ≤
      sd * ((star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re) := by
    intro x y
    rw [s14_polar, map_smul, map_sub, map_add, map_sub, map_smul, map_smul]
    refine (tn_smul_le _ _).trans ?_
    have h1 := hpure (x + y)
    have h2 := hpure (x - y)
    have h3 := hpure (x + Complex.I • y)
    have h4 := hpure (x - Complex.I • y)
    have h3' := tn_smul_le Complex.I (L (vecMulVec (x + Complex.I • y) (star (x + Complex.I • y))))
    have h4' := tn_smul_le Complex.I (L (vecMulVec (x - Complex.I • y) (star (x - Complex.I • y))))
    have t1 := s14_tn_sub (L (vecMulVec (x + y) (star (x + y))) - L (vecMulVec (x - y) (star (x - y))) +
      Complex.I • L (vecMulVec (x + Complex.I • y) (star (x + Complex.I • y))))
      (Complex.I • L (vecMulVec (x - Complex.I • y) (star (x - Complex.I • y))))
    have t2 := tn_add_le (L (vecMulVec (x + y) (star (x + y))) - L (vecMulVec (x - y) (star (x - y))))
      (Complex.I • L (vecMulVec (x + Complex.I • y) (star (x + Complex.I • y))))
    have t3 := s14_tn_sub (L (vecMulVec (x + y) (star (x + y)))) (L (vecMulVec (x - y) (star (x - y))))
    have hn := s14_polar_norm x y
    simp only [Complex.norm_I, one_mul] at h3' h4'
    have h14 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
    rw [h14]
    have hn' := congrArg (sd * ·) hn
    nlinarith
  obtain ⟨a, b, hX, ha, hb⟩ := rank_one_dec X
  nth_rewrite 1 [hX]
  rw [s14_idT_sum]
  refine (tn_sum_le _ _).trans ?_
  have hj : ∀ j, traceNorm (idTensorSuperop (R := Q) (⇑L) (vecMulVec (a j) (star (b j)))) ≤
      Fintype.card Q * sd * ((star (a j) ⬝ᵥ a j).re + (star (b j) ⬝ᵥ b j).re) := by
    intro j
    rw [s14_idT_rank1]
    refine (tn_sum_le _ _).trans ?_
    calc ∑ r, traceNorm (∑ s, (s14_iota r : Matrix (Q × B) B ℂ) * (L (vecMulVec (fun i => a j (r, i))
            (star fun i => b j (s, i))) : Matrix B B ℂ) * ((s14_iota s)ᴴ : Matrix B (Q × B) ℂ))
        ≤ ∑ r, ∑ s, sd * ((star (fun i => a j (r, i)) ⬝ᵥ (fun i => a j (r, i))).re +
            (star (fun i => b j (s, i)) ⬝ᵥ (fun i => b j (s, i))).re) := by
          refine Finset.sum_le_sum fun r _ => (tn_sum_le _ _).trans ?_
          refine Finset.sum_le_sum fun s _ => ?_
          refine (s14_contr _ _ (s14_iota_norm r) (s14_iota_norm s) _).trans ?_
          exact hr1 _ _
      _ = Fintype.card Q * sd * ((star (a j) ⬝ᵥ a j).re + (star (b j) ⬝ᵥ b j).re) := by
          rw [s14_normsplit (a j), s14_normsplit (b j)]
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
          ring
  calc ∑ j, traceNorm (idTensorSuperop (R := Q) (⇑L) (vecMulVec (a j) (star (b j))))
      ≤ ∑ j, Fintype.card Q * sd * ((star (a j) ⬝ᵥ a j).re + (star (b j) ⬝ᵥ b j).re) :=
        Finset.sum_le_sum fun j _ => hj j
    _ = 2 * Fintype.card Q * sd * traceNorm X := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ha, hb]; ring

end s14b

section s14c
variable {Q B : Type} [Fintype Q] [DecidableEq Q] [Fintype B] [DecidableEq B]

lemma s14_iota_iso (r : Q) : (s14_iota (Q := Q) (B := B) r)ᴴ * s14_iota (Q := Q) (B := B) r = 1 := by
  ext k k'
  simp only [s14_iota, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fintype.sum_prod_type]
  by_cases h : k = k'
  · simp [Matrix.one_apply, h, apply_ite star]
  · simp [Matrix.one_apply, h, apply_ite star, Ne.symm h]

omit [DecidableEq Q] in
lemma s14_hm [DecidableEq Q] (r : Q) (M : Matrix B B ℂ) (p q : Q) (i i' : B) :
    ((s14_iota (Q := Q) (B := B) r) * M * (s14_iota (Q := Q) (B := B) r)ᴴ) (p, i) (q, i') =
      if p = r ∧ q = r then M i i' else 0 := by
  simp only [s14_iota, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases hp : p = r <;> by_cases hq : q = r <;>
    simp [hp, hq, Matrix.one_apply, apply_ite star, ite_mul, mul_ite]

lemma s14_idT_embed (T : Matrix Q Q ℂ → Matrix B B ℂ) (hT0 : T 0 = 0) (r : Q) (ρ : Matrix Q Q ℂ) :
    idTensorSuperop (R := Q) T ((s14_iota (Q := Q) (B := Q) r) * ρ * (s14_iota (Q := Q) (B := Q) r)ᴴ) =
      (s14_iota (Q := Q) (B := B) r) * T ρ * (s14_iota (Q := Q) (B := B) r)ᴴ := by
  ext ⟨p, i⟩ ⟨q, i'⟩
  rw [s14_hm]
  simp only [idTensorSuperop, Matrix.of_apply, s14_hm]
  by_cases h : p = r ∧ q = r
  · simp only [h, and_self, if_true]; rfl
  · simp only [h, if_false]
    rw [show (Matrix.of fun (_ : Q) (_ : Q) => (0 : ℂ)) = 0 from rfl, hT0]; rfl
end s14c

open QAlgorithms.Papers.Independent.Advance50.P43 QAlgorithms.Papers.Independent.Information100.P69 in
theorem solution {B Q : Type} [Fintype B] [Fintype Q] [DecidableEq B] [DecidableEq Q]
    [Nonempty Q] [Nonempty B]
    (Phi Psi : Superop Q B)
    (hPhi : IsChannel Phi) (hPsi : IsChannel Psi) :
    stateDistance Phi Psi ≤ diamond (Phi - Psi) ∧
      diamond (Phi - Psi) ≤ 2 * (Fintype.card Q : ℝ) * stateDistance Phi Psi := by
  obtain ⟨L, hL⟩ := s14_lin Phi Psi hPhi hPsi
  have hdef : (Phi - Psi) = ⇑L := funext fun X => (hL X).symm
  set sd := stateDistance Phi Psi with hsd
  have hS_bdd : BddAbove {v | ∃ ρ : Matrix Q Q ℂ, IsDensityMatrix ρ ∧
      v = traceNorm (Phi ρ - Psi ρ)} := ⟨2, by
    rintro v ⟨ρ, hρ, rfl⟩; exact s14_bdd Phi Psi hPhi hPsi ρ hρ⟩
  have hsdρ : ∀ ρ, IsDensityMatrix ρ → traceNorm (L ρ) ≤ sd := fun ρ hρ => by
    rw [hL]; exact le_csSup hS_bdd ⟨ρ, hρ, rfl⟩
  obtain ⟨i0⟩ := (inferInstance : Nonempty Q)
  set ρ0 : Matrix Q Q ℂ := Matrix.diagonal (fun i => if i = i0 then (1 : ℂ) else 0) with hρ0def
  have hρ0 : IsDensityMatrix ρ0 := by
    refine ⟨?_, ?_⟩
    · rw [hρ0def, Matrix.posSemidef_diagonal_iff]
      intro i; split_ifs <;> simp
    · simp [hρ0def, Matrix.trace_diagonal]
  have hsd0 : 0 ≤ sd := (tn_nonneg _).trans (hsdρ ρ0 hρ0)
  have hpure : ∀ w : Q → ℂ, traceNorm (L (vecMulVec w (star w))) ≤ sd * (star w ⬝ᵥ w).re := by
    intro w
    have hn0 : 0 ≤ (star w ⬝ᵥ w).re := dot_star_re_nonneg w
    have hdr := dot_star_real w
    rcases hn0.lt_or_eq with hpos | hzero
    · set n := (star w ⬝ᵥ w).re with hn
      set ρ : Matrix Q Q ℂ := ((n : ℂ)⁻¹) • vecMulVec w (star w) with hρdef
      have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      have hρ : IsDensityMatrix ρ := by
        refine ⟨?_, ?_⟩
        · refine (posSemidef_vecMulVec_self_star w).smul ?_
          rw [← Complex.ofReal_inv]
          exact Complex.zero_le_real.mpr (inv_nonneg.mpr hn0)
        · rw [hρdef, Matrix.trace_smul, Matrix.trace_vecMulVec, dotProduct_comm, hdr, smul_eq_mul,
            inv_mul_cancel₀ hnc]
      have hw : vecMulVec w (star w) = (n : ℂ) • ρ := by
        rw [hρdef, smul_smul, mul_inv_cancel₀ hnc, one_smul]
      rw [hw, map_smul]
      refine (tn_smul_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_of_nonneg hn0]
      have := mul_le_mul_of_nonneg_left (hsdρ ρ hρ) hn0
      linarith
    · have h0 : star w ⬝ᵥ w = 0 := by rw [hdr, ← hzero]; simp
      have hw0 : w = 0 := dotProduct_star_self_eq_zero.mp h0
      subst hw0
      simp [tn_zero]
  have hdiam : ∀ X : Matrix (Q × Q) (Q × Q) ℂ, traceNorm X ≤ 1 →
      traceNorm (idTensorSuperop (R := Q) (Phi - Psi) X) ≤ 2 * (Fintype.card Q : ℝ) * sd := by
    intro X hX
    rw [hdef]
    refine (s14_main L sd hpure X).trans ?_
    have : 0 ≤ 2 * (Fintype.card Q : ℝ) * sd := by positivity
    nlinarith
  have hD_bdd : BddAbove {v | ∃ X : Matrix (Q × Q) (Q × Q) ℂ, traceNorm X ≤ 1 ∧
      v = traceNorm (idTensorSuperop (R := Q) (Phi - Psi) X)} := ⟨_, by
    rintro v ⟨X, hX, rfl⟩; exact hdiam X hX⟩
  refine ⟨?_, ?_⟩
  · rw [hsd]; unfold stateDistance
    refine csSup_le ⟨_, ρ0, hρ0, rfl⟩ ?_
    rintro v ⟨ρ, hρ, rfl⟩
    set X0 := (s14_iota (Q := Q) (B := Q) i0) * ρ * (s14_iota (Q := Q) (B := Q) i0)ᴴ
    have hX0 : traceNorm X0 ≤ 1 := by
      refine (s14_contr _ _ (s14_iota_norm i0) (s14_iota_norm i0) ρ).trans ?_
      have := g55b_tn_psd hρ.1
      rw [hρ.2] at this
      have : traceNorm ρ = 1 := by exact_mod_cast this
      linarith
    have hT0 : (Phi - Psi) 0 = 0 := by rw [hdef]; exact map_zero L
    have hemb := s14_idT_embed (Phi - Psi) hT0 i0 ρ
    have hle : traceNorm (Phi ρ - Psi ρ) ≤ traceNorm (idTensorSuperop (R := Q) (Phi - Psi) X0) := by
      rw [hemb]
      have hiso := s14_iota_iso (Q := Q) (B := B) i0
      have e : Phi ρ - Psi ρ = (s14_iota (Q := Q) (B := B) i0)ᴴ *
          ((s14_iota (Q := Q) (B := B) i0) * (Phi - Psi) ρ * (s14_iota (Q := Q) (B := B) i0)ᴴ) *
          ((s14_iota (Q := Q) (B := B) i0)ᴴ)ᴴ := by
        rw [Matrix.conjTranspose_conjTranspose]
        simp only [← Matrix.mul_assoc]
        rw [hiso, Matrix.one_mul, Matrix.mul_assoc, hiso, Matrix.mul_one]; rfl
      rw [e]
      exact s14_contr _ _ (s14_iotaH_norm i0) (s14_iotaH_norm i0) _
    exact hle.trans (le_csSup hD_bdd ⟨X0, hX0, rfl⟩)
  · unfold diamond
    refine csSup_le ⟨_, 0, by simp [tn_zero], rfl⟩ ?_
    rintro v ⟨X, hX, rfl⟩
    exact hdiam X hX
