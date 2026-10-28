-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P24.large_corner_near_private_bit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:20:56.456677+00:00
-- url     : https://prove2.me/submissions/3c921b37-4db3-4c75-8ad5-7902a01d1d63

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

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

lemma g55bq3_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma g55bq3_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma g55bq3_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    QAlgorithms.traceNorm X =
      (cfc (fun t : ℝ => max t 0) X).trace.re + (cfc (fun t : ℝ => max (-t) 0) X).trace.re := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  unfold QAlgorithms.traceNorm
  rw [hX.eq]
  have h1 : X * X = cfc (fun t : ℝ => t * t) X := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) X, cfc_id' ℝ X]
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) X, ← Complex.add_re, ← Matrix.trace_add,
    ← cfc_add X (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
  congr 2
  apply cfc_congr
  intro t _
  simp only [Function.comp]
  rw [← sq, Real.sqrt_sq_eq_abs]
  rcases le_total t 0 with h | h
  · rw [abs_of_nonpos h]; simp [h]
  · rw [abs_of_nonneg h]; simp [h]


namespace G55BS
open G55BF
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- generalized weighted FvdG for PSD A B without normalization -/
lemma fvdg2 {A B Z : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) (hZ : Z.IsHermitian)
    (h : (1 - Z * Z).PosSemidef) :
    (Z * (A - B)).trace.re ≤
      Real.sqrt ((A.trace.re + B.trace.re) ^ 2 -
        4 * ((cfc Real.sqrt (cfc Real.sqrt A * B * cfc Real.sqrt A)).trace.re) ^ 2) := by
  set Rρ := cfc Real.sqrt A with hRρ
  set Rσ := cfc Real.sqrt B with hRσ
  have hRρH : Rρᴴ = Rρ := (g55bq_sqrt_psd A).1.eq
  have hRσH : Rσᴴ = Rσ := (g55bq_sqrt_psd B).1.eq
  have hRρ2 : Rρ * Rρ = A := sqrt_mul_sqrt hA
  have hRσ2 : Rσ * Rσ = B := sqrt_mul_sqrt hB
  obtain ⟨W, hW, hpol⟩ := g55bq_polar (Rσ * Rρ)
  have hKK : (Rσ * Rρ)ᴴ * (Rσ * Rρ) = Rρ * B * Rρ := by
    rw [Matrix.conjTranspose_mul, hRρH, hRσH, Matrix.mul_assoc, ← Matrix.mul_assoc Rσ, hRσ2,
      Matrix.mul_assoc]
  rw [hKK] at hpol
  set Ab := cfc Real.sqrt (Rρ * B * Rρ) with hAb
  have hAbH : Abᴴ = Ab := (g55bq_sqrt_psd _).1.eq
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  set X : Matrix n n ℂ := Rρ with hX
  set Y : Matrix n n ℂ := Rσ * W with hY
  have hXX : X * Xᴴ = A := by rw [hX, hRρH, hRρ2]
  have hYY : Y * Yᴴ = B := by
    rw [hY, Matrix.conjTranspose_mul, hRσH, Matrix.mul_assoc, ← Matrix.mul_assoc W, hW', Matrix.one_mul, hRσ2]
  have fX : fq X = A.trace.re := by rw [fq_tr, hXX]
  have fY : fq Y = B.trace.re := by rw [fq_tr, hYY]
  set F := (Ab.trace).re with hF
  have hXY : (Xᴴ * Y).trace.re = F := by
    have hK : Rρ * Rσ = Ab * Wᴴ := by
      have := congrArg Matrix.conjTranspose hpol
      rw [Matrix.conjTranspose_mul, hRρH, hRσH, Matrix.conjTranspose_mul, hAbH] at this
      exact this
    rw [hX, hY, hRρH, ← Matrix.mul_assoc, hK, Matrix.mul_assoc, hW, Matrix.mul_one]
  have hcore := core X Y Z hZ h
  rw [hXX, hYY] at hcore
  refine hcore.trans (le_of_eq ?_)
  rw [← Real.sqrt_mul (fq_nonneg _), fq_add, fq_sub, fX, fY, hXY]
  congr 1; ring

/-- Re tr(√A √B) ≤ root fidelity. -/
lemma re_tr_le_rf {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (cfc Real.sqrt A * cfc Real.sqrt B).trace.re ≤
      (cfc Real.sqrt (cfc Real.sqrt A * B * cfc Real.sqrt A)).trace.re := by
  set Rρ := cfc Real.sqrt A with hRρ
  set Rσ := cfc Real.sqrt B with hRσ
  have hRρH : Rρᴴ = Rρ := (g55bq_sqrt_psd A).1.eq
  have hRσH : Rσᴴ = Rσ := (g55bq_sqrt_psd B).1.eq
  have hRσ2 : Rσ * Rσ = B := sqrt_mul_sqrt hB
  obtain ⟨W, hW, hpol⟩ := g55bq_polar (Rσ * Rρ)
  have hKK : (Rσ * Rρ)ᴴ * (Rσ * Rρ) = Rρ * B * Rρ := by
    rw [Matrix.conjTranspose_mul, hRρH, hRσH, Matrix.mul_assoc, ← Matrix.mul_assoc Rσ, hRσ2,
      Matrix.mul_assoc]
  rw [hKK] at hpol
  set P := cfc Real.sqrt (Rρ * B * Rρ) with hP
  have hPpsd : P.PosSemidef := g55bq_sqrt_psd _
  set Q := cfc Real.sqrt P with hQ
  have hQH : Qᴴ = Q := (g55bq_sqrt_psd P).1.eq
  have hQ2 : Q * Q = P := sqrt_mul_sqrt hPpsd
  have h1 : (Rρ * Rσ).trace.re = (Rσ * Rρ).trace.re := by rw [Matrix.trace_mul_comm]
  rw [h1, hpol]
  have h2 : (W * P).trace = (Qᴴ * (W * Q)).trace := by
    rw [hQH, ← hQ2, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [h2]
  have hc := cs Q (W * Q)
  have fQ : fq Q = P.trace.re := by unfold fq; rw [hQH, hQ2]
  have fWQ : fq (W * Q) = P.trace.re := by
    unfold fq
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hW, Matrix.one_mul, hQH, hQ2]
  rw [fQ, fWQ, Real.mul_self_sqrt (fq_nonneg Q |>.trans_eq fQ)] at hc
  exact hc

lemma sgn_trace {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∃ Z : Matrix n n ℂ, Z.IsHermitian ∧ (1 - Z * Z).PosSemidef ∧
      (Z * H).trace.re = QAlgorithms.traceNorm H := by
  have hsa : IsSelfAdjoint H := hH.isSelfAdjoint
  have hfin := H.finite_real_spectrum
  set g : ℝ → ℝ := fun t => if 0 ≤ t then 1 else -1 with hg
  refine ⟨cfc g H, (cfc_predicate g H).isHermitian, ?_, ?_⟩
  · have : 1 - cfc g H * cfc g H = 0 := by
      rw [← cfc_mul g g H (hfin.continuousOn _) (hfin.continuousOn _), ← cfc_one ℝ H,
        ← cfc_sub (1 : ℝ → ℝ) (fun t => g t * g t) H (hfin.continuousOn _) (hfin.continuousOn _)]
      rw [← cfc_zero ℝ H]
      apply cfc_congr
      intro t _
      simp only [hg, Pi.one_apply]
      split_ifs <;> norm_num
    rw [this]; exact Matrix.PosSemidef.zero
  · rw [g55bq3_traceNorm_herm hH, ← Complex.add_re, ← Matrix.trace_add,
      ← cfc_add H (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
    have : cfc g H * H = cfc (fun t => g t * t) H := by
      rw [cfc_mul g (fun t : ℝ => t) H (hfin.continuousOn _) (hfin.continuousOn _), cfc_id' ℝ H]
    rw [this]
    congr 3
    funext t
    simp only [hg]
    rcases le_total 0 t with h | h
    · simp [h]
    · rcases eq_or_lt_of_le h with h' | h'
      · simp [h']
      · simp [not_le.mpr h', h'.le]

/-- the Powers–Størmer step: Re tr(Z(A-B)) ≥ ‖√A - √B‖₂² for Z = sign(√A - √B). -/
lemma ps {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    fq (cfc Real.sqrt A - cfc Real.sqrt B) ≤ QAlgorithms.traceNorm (A - B) := by
  set Ra := cfc Real.sqrt A
  set Rb := cfc Real.sqrt B
  have hRa : Ra.PosSemidef := g55bq_sqrt_psd A
  have hRb : Rb.PosSemidef := g55bq_sqrt_psd B
  set S := Ra - Rb with hS
  set T := Ra + Rb with hT
  have hSH : S.IsHermitian := hRa.1.sub hRb.1
  have hsa : IsSelfAdjoint S := hSH.isSelfAdjoint
  have hfin := S.finite_real_spectrum
  have hHH : (A - B).IsHermitian := hA.1.sub hB.1
  -- the sign of S
  set g : ℝ → ℝ := fun t => if 0 ≤ t then 1 else -1 with hg
  set Z := cfc g S with hZ
  have hZH : Z.IsHermitian := (cfc_predicate g S).isHermitian
  have hZ1 : (1 - Z).PosSemidef := by
    rw [hZ, ← cfc_one ℝ S, ← cfc_sub (1 : ℝ → ℝ) g S (hfin.continuousOn _) (hfin.continuousOn _)]
    apply g55bq3_cfc_psd
    intro t; simp only [hg, Pi.one_apply]; split_ifs <;> norm_num
  have hZ2 : (1 + Z).PosSemidef := by
    rw [hZ, ← cfc_one ℝ S, ← cfc_add S (1 : ℝ → ℝ) g (hfin.continuousOn _) (hfin.continuousOn _)]
    apply g55bq3_cfc_psd
    intro t; simp only [hg, Pi.one_apply]; split_ifs <;> norm_num
  -- trace norm dominates
  have hdom : (Z * (A - B)).trace.re ≤ QAlgorithms.traceNorm (A - B) := by
    rw [g55bq3_traceNorm_herm hHH]
    have hparts := g55bq3_parts (A - B) hHH
    set Hp := cfc (fun t : ℝ => max t 0) (A - B)
    set Hm := cfc (fun t : ℝ => max (-t) 0) (A - B)
    have hp : Hp.PosSemidef := g55bq3_cfc_psd _ _ (fun t => le_max_right _ _)
    have hm : Hm.PosSemidef := g55bq3_cfc_psd _ _ (fun t => le_max_right _ _)
    have h1 := tr_psd_mul hZ1 hp
    have h2 := tr_psd_mul hZ2 hm
    rw [← hparts, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at h1
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, Complex.add_re] at h2
    linarith
  refine le_trans ?_ hdom
  -- A - B = (S T + T S)/2
  have hRa2 : Ra * Ra = A := sqrt_mul_sqrt hA
  have hRb2 : Rb * Rb = B := sqrt_mul_sqrt hB
  have hAB : A - B = (1 / 2 : ℂ) • (S * T + T * S) := by
    rw [← hRa2, ← hRb2, hS, hT]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.add_mul, Matrix.sub_mul,
      Matrix.mul_add, Matrix.mul_sub, smul_eq_mul]
    ring
  -- Z S = S Z = |S| = Sp + Sm
  set Sp := cfc (fun t : ℝ => max t 0) S
  set Sm := cfc (fun t : ℝ => max (-t) 0) S
  have hSp : Sp.PosSemidef := g55bq3_cfc_psd _ _ (fun t => le_max_right _ _)
  have hSm : Sm.PosSemidef := g55bq3_cfc_psd _ _ (fun t => le_max_right _ _)
  have habs : ∀ t : ℝ, g t * t = max t 0 + max (-t) 0 := by
    intro t; simp only [hg]
    rcases le_total 0 t with h | h
    · simp [h]
    · rcases eq_or_lt_of_le h with h' | h'
      · simp [h']
      · simp [not_le.mpr h', h'.le]
  have hZS : Z * S = Sp + Sm := by
    conv_lhs => rw [show S = cfc (fun t : ℝ => t) S from (cfc_id' ℝ S).symm]
    rw [hZ, ← cfc_mul g (fun t : ℝ => t) S (hfin.continuousOn _) (hfin.continuousOn _), ← cfc_add S (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
    exact cfc_congr (fun t _ => habs t)
  have hSZ : S * Z = Sp + Sm := by
    conv_lhs => rw [show S = cfc (fun t : ℝ => t) S from (cfc_id' ℝ S).symm]
    rw [hZ, ← cfc_mul (fun t : ℝ => t) g S (hfin.continuousOn _) (hfin.continuousOn _), ← cfc_add S (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
    exact cfc_congr (fun t _ => by rw [mul_comm]; exact habs t)
  have htr : (Z * (A - B)).trace = ((Sp + Sm) * T).trace := by
    rw [hAB, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add,
      ← Matrix.mul_assoc, hZS, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, hSZ]
    rw [smul_eq_mul]; ring
  rw [htr]
  -- T - S = 2 Rb, T + S = 2 Ra
  have hTS1 : ((Sp) * (T - S)).trace.re ≥ 0 := by
    have : T - S = (2 : ℂ) • Rb := by rw [hT, hS]; module
    rw [this]; exact tr_psd_mul hSp (hRb.smul (by norm_num))
  have hTS2 : ((Sm) * (T + S)).trace.re ≥ 0 := by
    have : T + S = (2 : ℂ) • Ra := by rw [hT, hS]; module
    rw [this]; exact tr_psd_mul hSm (hRa.smul (by norm_num))
  have hparts := g55bq3_parts S hSH
  have hfq : fq S = ((Sp - Sm) * S).trace.re := by
    unfold fq; rw [hSH.eq, hparts]
  rw [hfq]
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hTS1
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re] at hTS2
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
  linarith

end G55BS



open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

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

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P24

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

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

lemma g55b_tw_left {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
    (U : Key d → Matrix.unitaryGroup H ℂ) (a : Key d) (s : H) (f : Key d × H → ℂ) :
    ∑ x, twistingMatrix U (a, s) x * f x = ∑ u, (U a : Op H) s u * f (a, u) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [twistingMatrix]
  · intro k _ hk
    simp [twistingMatrix, Ne.symm hk]
  · simp

lemma g55b_tw_right {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
    (U : Key d → Matrix.unitaryGroup H ℂ) (b : Key d) (t : H) (f : Key d × H → ℂ) :
    ∑ x, f x * star (twistingMatrix U (b, t) x) = ∑ u, f (b, u) * star ((U b : Op H) t u) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp [twistingMatrix]
  · intro k _ hk
    simp [twistingMatrix, Ne.symm hk]
  · simp

lemma g55b_twist_block {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
    (U : Key d → Matrix.unitaryGroup H ℂ) (rho : Op (Key d × H)) (a b : Key d) :
    keyBlock (twist U rho) a b = (U a : Op H) * keyBlock rho a b * (U b : Op H)ᴴ := by
  ext s t
  simp only [keyBlock, twist, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [g55b_tw_right U b t (fun x => ∑ j, twistingMatrix U (a, s) j * rho j x)]
  simp only [g55b_tw_left]

lemma g55b_traceRight_twist {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
    (U : Key d → Matrix.unitaryGroup H ℂ) (rho : Op (Key d × H)) (a b : Key d) :
    traceRight (twist U rho) a b = ((U a : Op H) * keyBlock rho a b * (U b : Op H)ᴴ).trace := by
  rw [← g55b_twist_block]; rfl


def g55b_bd {L H : Type*} (D : L → Op H) : Op (L × H) :=
  fun a b => if a.1 = b.1 then D a.1 a.2 b.2 else 0

lemma g55b_bd_mul {L H : Type*} [Fintype L] [Fintype H] (D E : L → Op H) :
    g55b_bd D * g55b_bd E = g55b_bd (fun k => D k * E k) := by
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single a.1]
  · simp only [g55b_bd, if_true]
    by_cases h : a.1 = b.1
    · simp [h, Matrix.mul_apply]
    · simp [h]
  · intro k _ hk
    simp [g55b_bd, Ne.symm hk]
  · simp

lemma g55b_bd_ct {L H : Type*} (D : L → Op H) :
    (g55b_bd D)ᴴ = g55b_bd (fun k => (D k)ᴴ) := by
  ext a b
  simp only [g55b_bd, Matrix.conjTranspose_apply]
  by_cases h : a.1 = b.1
  · rw [if_pos h.symm, if_pos h, h]
  · rw [if_neg (Ne.symm h), if_neg h]; simp

lemma g55b_bd_trace {L H : Type*} [Fintype L] [Fintype H] (D : L → Op H) :
    (g55b_bd D).trace = ∑ k, (D k).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, g55b_bd, Fintype.sum_prod_type, if_true]

lemma g55b_bd_tn {L H : Type*} [Fintype L] [Fintype H] [DecidableEq L] [DecidableEq H]
    (p : L → ℝ) (hp : ∀ k, 0 ≤ p k) (D : L → Op H) :
    traceNorm (g55b_bd (fun k => (p k : ℂ) • D k)) = ∑ k, p k * traceNorm (D k) := by
  set Q : L → Op H := fun k => (p k : ℂ) • cfc Real.sqrt ((D k)ᴴ * D k) with hQ
  have hQp : ∀ k, (Q k).PosSemidef := fun k =>
    (g55b_sqrt_psd _).smul (Complex.zero_le_real.mpr (hp k))
  set R : L → Op H := fun k => cfc Real.sqrt (Q k) with hR
  have hRR : ∀ k, (R k)ᴴ * R k = Q k := by
    intro k
    rw [(g55b_sqrt_psd (Q k)).1.eq]
    exact G55BF.sqrt_mul_sqrt (hQp k)
  have hbQ : (g55b_bd Q).PosSemidef := by
    have : g55b_bd Q = (g55b_bd R)ᴴ * g55b_bd R := by
      rw [g55b_bd_ct, g55b_bd_mul]; simp only [hRR]
    rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have hsq : (g55b_bd (fun k => (p k : ℂ) • D k))ᴴ * g55b_bd (fun k => (p k : ℂ) • D k) =
      g55b_bd Q * g55b_bd Q := by
    rw [g55b_bd_ct, g55b_bd_mul, g55b_bd_mul]
    congr 1
    funext k
    simp only [hQ, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      g55b_sqrt_mul_self, Complex.star_def, Complex.conj_ofReal]
  unfold traceNorm
  rw [hsq, g55b_sqrt_sq hbQ, g55b_bd_trace, Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [hQ, Matrix.trace_smul]

lemma g55b_fid_le_one {H : Type*} [Fintype H] [DecidableEq H] {A B : Op H}
    (hA : IsDensityMatrix A) (hB : IsDensityMatrix B) : rootFidelity A B ≤ 1 := by
  set a := cfc Real.sqrt A
  set b := cfc Real.sqrt B
  have ha : aᴴ = a := (g55b_sqrt_psd A).1.eq
  have hb : bᴴ = b := (g55b_sqrt_psd B).1.eq
  have haa : a * a = A := G55BF.sqrt_mul_sqrt hA.1
  have hbb : b * b = B := G55BF.sqrt_mul_sqrt hB.1
  have hF : rootFidelity A B = traceNorm (b * a) := by
    have e : (b * a)ᴴ * (b * a) = a * B * a := by
      rw [Matrix.conjTranspose_mul, ha, hb, Matrix.mul_assoc, ← Matrix.mul_assoc b b, hbb,
        ← Matrix.mul_assoc]
    unfold rootFidelity traceNorm
    rw [e]
  obtain ⟨W, hW, hW', h1, -, -⟩ := g55b_polar_tr (b * a)
  have hc := G55BF.cs (b * W) a
  have e1 : ((b * W)ᴴ * a).trace = traceNorm (b * a) := by
    rw [Matrix.conjTranspose_mul, hb, Matrix.mul_assoc, h1]
  have f1 : G55BF.fq (b * W) = 1 := by
    unfold G55BF.fq
    rw [Matrix.conjTranspose_mul, hb, Matrix.mul_assoc, ← Matrix.mul_assoc b, hbb,
      ← Matrix.mul_assoc, Matrix.trace_mul_cycle, hW', Matrix.one_mul, hB.2]; simp
  have f2 : G55BF.fq a = 1 := by
    unfold G55BF.fq; rw [ha, haa, hA.2]; simp
  rw [e1, f1, f2] at hc
  simp at hc
  rw [hF]; exact hc

lemma g55b_fvdg_lo {H : Type*} [Fintype H] [DecidableEq H] {A B : Op H}
    (hA : IsDensityMatrix A) (hB : IsDensityMatrix B) :
    1 - traceNorm (A - B) / 2 ≤ rootFidelity A B := by
  have h1 := G55BS.ps hA.1 hB.1
  rw [G55BF.fq_sub] at h1
  have hRaH : (cfc Real.sqrt A)ᴴ = cfc Real.sqrt A := (g55b_sqrt_psd A).1.eq
  have fa : G55BF.fq (cfc Real.sqrt A) = 1 := by
    unfold G55BF.fq; rw [hRaH, G55BF.sqrt_mul_sqrt hA.1, hA.2]; simp
  have fb : G55BF.fq (cfc Real.sqrt B) = 1 := by
    unfold G55BF.fq; rw [(g55b_sqrt_psd B).1.eq, G55BF.sqrt_mul_sqrt hB.1, hB.2]; simp
  have h2 := G55BS.re_tr_le_rf hA.1 hB.1
  rw [fa, fb, hRaH] at h1
  unfold rootFidelity
  linarith

lemma g55b_fvdg_hi {H : Type*} [Fintype H] [DecidableEq H] {A B : Op H}
    (hA : IsDensityMatrix A) (hB : IsDensityMatrix B) :
    traceNorm (A - B) ≤ Real.sqrt (8 * (1 - rootFidelity A B)) := by
  obtain ⟨Z, hZ, hZ2, hZt⟩ := G55BS.sgn_trace (hA.1.1.sub hB.1.1)
  have h := G55BS.fvdg2 hA.1 hB.1 hZ hZ2
  rw [hZt, hA.2, hB.2] at h
  refine h.trans (Real.sqrt_le_sqrt ?_)
  have : (cfc Real.sqrt (cfc Real.sqrt A * B * cfc Real.sqrt A)).trace.re = rootFidelity A B := rfl
  rw [this]
  simp
  nlinarith [sq_nonneg (1 - rootFidelity A B)]

namespace S64LC

section rect
variable {m n : Type*} [Fintype m] [Fintype n]

/-- Frobenius square for rectangular matrices. -/
noncomputable def fr (X : Matrix m n ℂ) : ℝ := (Xᴴ * X).trace.re

lemma fr_nonneg (X : Matrix m n ℂ) : 0 ≤ fr X := by
  classical
  have := (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg
  exact (Complex.nonneg_iff.mp this).1

lemma re_tr_swap' (P Q : Matrix m n ℂ) : (Qᴴ * P).trace.re = (Pᴴ * Q).trace.re := by
  have : (Qᴴ * P).trace = star ((Pᴴ * Q).trace) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [this]; simp

lemma fr_sub (X Y : Matrix m n ℂ) : fr (X - Y) = fr X + fr Y - 2 * (Xᴴ * Y).trace.re := by
  unfold fr
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.trace_sub, Matrix.trace_sub, Complex.sub_re, Complex.sub_re, Complex.sub_re,
    re_tr_swap' Y X]
  ring

lemma fr_smul (c : ℝ) (X : Matrix m n ℂ) : fr ((c : ℂ) • X) = c ^ 2 * fr X := by
  unfold fr
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul]
  have : star (c:ℂ) * (c:ℂ) = ((c^2:ℝ):ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
  rw [this, smul_eq_mul, Complex.re_ofReal_mul]

lemma cs' (P Q : Matrix m n ℂ) : (Pᴴ * Q).trace.re ≤ Real.sqrt (fr P) * Real.sqrt (fr Q) := by
  have hq : ∀ t : ℝ, 0 ≤ fr Q * (t * t) + (-2 * (Pᴴ * Q).trace.re) * t + fr P := by
    intro t
    have h := fr_nonneg (P - (t : ℂ) • Q)
    rw [fr_sub, fr_smul] at h
    have e : (Pᴴ * ((t : ℂ) • Q)).trace.re = t * (Pᴴ * Q).trace.re := by
      rw [Matrix.mul_smul, Matrix.trace_smul]; simp
    rw [e] at h
    nlinarith [h]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have h2 : ((Pᴴ * Q).trace.re) ^ 2 ≤ fr P * fr Q := by nlinarith
  calc (Pᴴ * Q).trace.re ≤ |(Pᴴ * Q).trace.re| := le_abs_self _
    _ = Real.sqrt (((Pᴴ * Q).trace.re) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (fr P * fr Q) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (fr P) * Real.sqrt (fr Q) := Real.sqrt_mul (fr_nonneg P) _

lemma fr_add_le (X Y : Matrix m n ℂ) :
    Real.sqrt (fr (X + Y)) ≤ Real.sqrt (fr X) + Real.sqrt (fr Y) := by
  have h := fr_sub X (-Y)
  rw [sub_neg_eq_add] at h
  have hn : fr (-Y) = fr Y := by unfold fr; simp
  have hc : (Xᴴ * -Y).trace.re = -(Xᴴ * Y).trace.re := by simp [Matrix.trace_neg]
  rw [hn, hc] at h
  have c := cs' X Y
  have s1 := Real.sqrt_nonneg (fr X)
  have s2 := Real.sqrt_nonneg (fr Y)
  rw [Real.sqrt_le_left (by positivity)]
  rw [h, add_sq, Real.sq_sqrt (fr_nonneg X), Real.sq_sqrt (fr_nonneg Y)]
  nlinarith

lemma fr_mul_unitary [DecidableEq n] (X : Matrix m n ℂ) {W : Matrix n n ℂ} (hW : W * Wᴴ = 1) :
    fr (X * W) = fr X := by
  unfold fr
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, hW, Matrix.mul_one]

end rect

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- column block of a matrix indexed by `Key 2 × H`. -/
def colB {m : Type*} (X : Matrix m (Key 2 × H) ℂ) (k : Key 2) : Matrix m H ℂ :=
  fun r s => X r (k, s)

def fromCols {m : Type*} (g : Key 2 → Matrix m H ℂ) : Matrix m (Key 2 × H) ℂ :=
  fun r j => g j.1 r j.2

lemma keyBlock_gram {m : Type*} [Fintype m] (X : Matrix m (Key 2 × H) ℂ) (a b : Key 2) :
    keyBlock (Xᴴ * X) a b = (colB X a)ᴴ * colB X b := by
  ext s t
  simp [keyBlock, colB, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma key_sum (f : Key 2 → ℝ) : ∑ k, f k = f (0,0) + f (0,1) + f (1,0) + f (1,1) := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]; ring

lemma fr_cols {m : Type*} [Fintype m] (X : Matrix m (Key 2 × H) ℂ) :
    fr X = ∑ k, fr (colB X k) := by
  unfold fr
  rw [← Complex.re_sum]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
  rfl

lemma tr_block {m : Type*} [Fintype m] (X : Matrix m (Key 2 × H) ℂ) (k : Key 2) :
    (keyBlock (Xᴴ * X) k k).trace.re = fr (colB X k) := by
  rw [keyBlock_gram]; rfl

lemma tn_le {N : Type*} [Fintype N] [DecidableEq N] (Z Z' : Matrix N N ℂ)
    (h1 : fr Z = 1) (h2 : fr Z' = 1) :
    traceNorm (Zᴴ * Z - Z'ᴴ * Z') ≤ 2 * Real.sqrt (fr (Z - Z')) := by
  obtain ⟨V, hV, hV', htr, -, -⟩ := g55b_polar_tr (Zᴴ * Z - Z'ᴴ * Z')
  have e : Zᴴ * Z - Z'ᴴ * Z' = Zᴴ * (Z - Z') + (Z - Z')ᴴ * Z' := by
    rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]; abel
  have hre : traceNorm (Zᴴ * Z - Z'ᴴ * Z') = (Vᴴ * (Zᴴ * Z - Z'ᴴ * Z')).trace.re := by
    rw [htr]; simp
  rw [hre, e, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  have t1 : (Vᴴ * (Zᴴ * (Z - Z'))).trace.re = ((Z * V)ᴴ * (Z - Z')).trace.re := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have t2 : (Vᴴ * ((Z - Z')ᴴ * Z')).trace.re = (((Z - Z') * V)ᴴ * Z').trace.re := by
    rw [Matrix.conjTranspose_mul (Z - Z'), Matrix.mul_assoc]
  rw [t1, t2]
  have c1 := cs' (Z * V) (Z - Z')
  have c2 := cs' ((Z - Z') * V) Z'
  rw [fr_mul_unitary _ hV', h1] at c1
  rw [fr_mul_unitary _ hV', h2] at c2
  rw [Real.sqrt_one, one_mul] at c1
  rw [Real.sqrt_one, mul_one] at c2
  linarith

lemma colB_fromCols {m : Type*} (g : Key 2 → Matrix m H ℂ) (k : Key 2) :
    colB (fromCols g) k = g k := rfl

lemma fr_zero {m : Type*} [Fintype m] : fr (0 : Matrix m H ℂ) = 0 := by unfold fr; simp

end S64LC

namespace S64LC2
open S64LC

variable {S T : Type} [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]

theorem near (rho : Op (Key 2 × (S × T))) (hrho : IsDensityMatrix rho) (eps : ℝ)
    (hpos : 0 < eps) (hlt : eps < 1/8)
    (hA : traceNorm (keyBlock rho (0,0) (1,1)) > 1/2 - eps) :
    ∃ gamma : Op (Key 2 × (S × T)), IsPrivate gamma ∧
      traceNorm (rho - gamma) ≤ 2 * (Real.sqrt (2 * eps) + 2 * Real.sqrt eps) := by
  set Z := cfc Real.sqrt rho with hZ
  have hZh : Zᴴ = Z := (g55b_sqrt_psd rho).1.eq
  have hZZ : Zᴴ * Z = rho := by rw [hZh]; exact G55BF.sqrt_mul_sqrt hrho.1
  set A := keyBlock rho (0,0) (1,1) with hAdef
  obtain ⟨W, hW, hW', htrW, -, -⟩ := g55b_polar_tr A
  set a := traceNorm A with hadef
  set Y0 := colB Z (0,0) with hY0
  set Y1 := colB Z (1,1) with hY1
  set x := fr Y0 with hx
  set y := fr Y1 with hy
  have hfrZ : fr Z = 1 := by unfold fr; rw [hZZ, hrho.2]; simp
  have hsum : fr Z = x + fr (colB Z (0,1)) + fr (colB Z (1,0)) + y := by
    rw [fr_cols, key_sum]
  have n01 := fr_nonneg (colB Z (0,1))
  have n10 := fr_nonneg (colB Z (1,0))
  have hA' : A = Y0ᴴ * Y1 := by rw [hAdef, ← hZZ, keyBlock_gram]
  have ha : a = ((Y0 * W)ᴴ * Y1).trace.re := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← hA', htrW]; simp
  have hx0 : 0 ≤ x := fr_nonneg Y0
  have hy0 : 0 ≤ y := fr_nonneg Y1
  have hcs : a ≤ Real.sqrt x * Real.sqrt y := by
    have := cs' (Y0 * W) Y1
    rw [fr_mul_unitary Y0 hW'] at this
    rw [ha]; exact this
  -- real estimates
  have hapos : 0 < a := by linarith
  have hxy : a ^ 2 ≤ x * y := by
    have := pow_le_pow_left₀ hapos.le hcs 2
    rwa [mul_pow, Real.sq_sqrt hx0, Real.sq_sqrt hy0] at this
  have hsq : (2 * x - 1) ^ 2 ≤ 4 * eps := by nlinarith
  have hxpos : 0 < x := by
    rcases hx0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hxy; nlinarith
  have h12a : 1 - 2 * a ≤ 2 * eps := by linarith
  -- construction
  set u : Fin 2 → Matrix (S × T) (S × T) ℂ := fun i => if i = 0 then 1 else Wᴴ with hu
  set g : Key 2 → Matrix (Key 2 × (S × T)) (S × T) ℂ :=
    fun k => if k.1 = k.2 then Y0 * (u k.1)ᴴ else 0 with hg
  have g00 : g (0,0) = Y0 := by simp [hg, hu]
  have g11 : g (1,1) = Y0 * W := by simp [hg, hu]
  have g01 : g (0,1) = 0 := by simp [hg]
  have g10 : g (1,0) = 0 := by simp [hg]
  set Z'' := fromCols g with hZ''
  set v := Real.sqrt (2 * x) with hv
  have hvpos : 0 < v := Real.sqrt_pos.2 (by linarith)
  have hvsq : v ^ 2 = 2 * x := Real.sq_sqrt (by linarith)
  set c := 1 / v with hc
  set Z' := (c : ℂ) • Z'' with hZ'
  set gamma := Z'ᴴ * Z' with hgamma
  have hfrZ'' : fr Z'' = 2 * x := by
    rw [fr_cols, key_sum]; simp only [hZ'', colB_fromCols, g00, g11, g01, g10, fr_zero,
      fr_mul_unitary Y0 hW']; ring
  have hfrZ' : fr Z' = 1 := by
    rw [hZ', fr_smul, hfrZ'', hc, ← hvsq]; field_simp
  have hD : fr (Z - Z'') = 1 - 2 * a := by
    rw [fr_cols, key_sum]
    have e : ∀ k, colB (Z - Z'') k = colB Z k - g k := fun k => rfl
    have e00 : colB (Z - Z'') (0,0) = 0 := by rw [e, g00, hY0, sub_self]
    have e01 : colB (Z - Z'') (0,1) = colB Z (0,1) := by rw [e, g01, sub_zero]
    have e10 : colB (Z - Z'') (1,0) = colB Z (1,0) := by rw [e, g10, sub_zero]
    have e11 : colB (Z - Z'') (1,1) = Y1 - Y0 * W := by rw [e, g11]
    rw [e00, e01, e10, e11, fr_zero, fr_sub, fr_mul_unitary Y0 hW', re_tr_swap' (Y0 * W) Y1, ← ha]
    linarith
  have hsplit : Z - Z' = (Z - Z'') + ((1 - c : ℝ) : ℂ) • Z'' := by
    rw [hZ']; push_cast; rw [sub_smul, one_smul]; abel
  have hb1 : Real.sqrt (fr (Z - Z')) ≤ Real.sqrt (2 * eps) + 2 * Real.sqrt eps := by
    rw [hsplit]
    refine (fr_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [hD]; exact Real.sqrt_le_sqrt h12a
    · rw [fr_smul, hfrZ'', ← hvsq, ← mul_pow, Real.sqrt_sq_eq_abs]
      have e : (1 - c) * v = v - 1 := by rw [hc]; field_simp
      rw [e]
      have h1 : |v - 1| ≤ |2 * x - 1| := by
        rw [← hvsq, show v ^ 2 - 1 = (v - 1) * (v + 1) by ring, abs_mul]
        have : |v + 1| = v + 1 := abs_of_pos (by linarith)
        rw [this]
        nlinarith [abs_nonneg (v - 1)]
      have h2 : |2 * x - 1| ≤ Real.sqrt (4 * eps) := Real.abs_le_sqrt hsq
      have h3 : Real.sqrt (4 * eps) = 2 * Real.sqrt eps := by
        rw [Real.sqrt_mul (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      linarith
  have hfrZ1 : fr Z = 1 := hfrZ
  have htn := tn_le Z Z' hfrZ1 hfrZ'
  rw [hZZ] at htn
  -- private structure
  have hcol : ∀ k, colB Z' k = (c : ℂ) • g k := fun k => rfl
  have hblock : ∀ k l, keyBlock gamma k l = ((c ^ 2 : ℝ) : ℂ) • ((g k)ᴴ * g l) := by
    intro k l
    rw [hgamma, keyBlock_gram, hcol, hcol, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
  have humem : ∀ i, u i ∈ Matrix.unitaryGroup (S × T) ℂ := by
    intro i
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    fin_cases i
    · simp [hu]
    · simp [hu, hW]
  set U : Fin 2 → Matrix.unitaryGroup (S × T) ℂ := fun i => ⟨u i, humem i⟩ with hU
  set tau : Op (S × T) := ((1 / x : ℝ) : ℂ) • (Y0ᴴ * Y0) with htau
  have hP : (Y0ᴴ * Y0).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Y0
  have htrP : (Y0ᴴ * Y0).trace = (x : ℂ) := by rw [g55b_psd_trace hP]; rfl
  refine ⟨gamma, ⟨⟨Matrix.posSemidef_conjTranspose_mul_self Z', ?_⟩, tau, ⟨?_, ?_⟩, U, ?_⟩, ?_⟩
  · rw [g55b_psd_trace (Matrix.posSemidef_conjTranspose_mul_self Z')]
    show (((fr Z' : ℝ)) : ℂ) = 1
    rw [hfrZ']; simp
  · exact hP.smul (Complex.zero_le_real.2 (by positivity))
  · rw [htau, Matrix.trace_smul, htrP, smul_eq_mul, ← Complex.ofReal_mul]
    rw [one_div, inv_mul_cancel₀ hxpos.ne']; simp
  · ext ⟨k, s⟩ ⟨l, t⟩
    have hb := congrFun (congrFun (hblock k l) s) t
    simp only [keyBlock] at hb
    rw [hb]
    unfold privateMatrix
    by_cases hk : k.1 = k.2
    · by_cases hl : l.1 = l.2
      · rw [if_pos ⟨hk, hl⟩]
        have hm : ((c ^ 2 : ℝ) : ℂ) • ((g k)ᴴ * g l) =
            ((2 : ℕ) : ℂ)⁻¹ • ((U k.1 : Op (S × T)) * tau * (U l.1 : Op (S × T))ᴴ) := by
          simp only [hg, if_pos hk, if_pos hl, hU, htau, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
          congr 1
          · rw [hc, div_pow, hvsq]; push_cast; field_simp
          · simp only [Matrix.mul_assoc]
        rw [hm]; rfl
      · rw [if_neg (fun h => hl h.2)]
        simp [hg, hl]
    · rw [if_neg (fun h => hk h.1)]
      simp [hg, hk]
  · exact htn.trans (by linarith [hb1])

end S64LC2

namespace S64LC3

lemma pbe_ge (eps : ℝ) (hpos : 0 < eps) (hlt : eps < 1/8) :
    2 * (Real.sqrt (2 * eps) + 2 * Real.sqrt eps) ≤ privateBitError eps := by
  unfold privateBitError
  set s := Real.sqrt (2 * eps) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 * eps := Real.sq_sqrt (by linarith)
  have hs1 : s < 1/2 := by nlinarith
  have hb : 0 ≤ binEntropy2 (2 * s) := by
    unfold binEntropy2
    exact div_nonneg (Real.binEntropy_nonneg (by linarith) (by linarith))
      (Real.log_nonneg (by norm_num))
  have he0 := Real.sqrt_nonneg eps
  have he2 : Real.sqrt eps ^ 2 = eps := Real.sq_sqrt hpos.le
  have h : 2 * Real.sqrt eps ≤ Real.sqrt (8 * s + binEntropy2 (2 * s)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  linarith

lemma pbe_cont : Continuous privateBitError := by
  have hb := Real.binEntropy_continuous
  unfold privateBitError binEntropy2
  fun_prop

lemma pbe_zero : privateBitError 0 = 0 := by
  simp [privateBitError, binEntropy2]

end S64LC3

theorem solution :
    Filter.Tendsto privateBitError (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    ∀ {S T : Type} [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
      (rho : Op (Key 2 × (S × T))), IsDensityMatrix rho →
      ∀ eps : ℝ, 0 < eps → eps < 1/8 → traceNorm (keyBlock rho (0,0) (1,1)) > 1/2-eps →
      ∃ gamma : Op (Key 2 × (S × T)), IsPrivate gamma ∧
        traceNorm (rho-gamma) ≤ privateBitError eps := by
  refine ⟨?_, ?_⟩
  · have := S64LC3.pbe_cont.tendsto 0
    rw [S64LC3.pbe_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · intro S T _ _ _ _ rho hrho eps hpos hlt hA
    obtain ⟨gamma, hg, hd⟩ := S64LC2.near rho hrho eps hpos hlt hA
    exact ⟨gamma, hg, hd.trans (S64LC3.pbe_ge eps hpos hlt)⟩

end
