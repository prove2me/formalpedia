-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P50.proposition_4_8
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:00:48.605914+00:00
-- url     : https://prove2.me/submissions/580a273f-221c-420f-9b6a-3081249e48f0

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

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

namespace S64FC
open G55BF Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma vmv_mul (a b c e : n → ℂ) :
    vecMulVec a b * vecMulVec c e = (b ⬝ᵥ c) • vecMulVec a e := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma cube_lemma {R : Type*} [Ring R] [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (X Y : R) (k : ℂ)
    (hX : X * X = X) (hY : Y * Y = Y) (hXYX : X * Y * X = k • X) (hYXY : Y * X * Y = k • Y) :
    (X - Y) * (X - Y) * (X - Y) = (1 - k) • (X - Y) := by
  have e : (X - Y) * (X - Y) * (X - Y) = X * X * X - X * X * Y - X * Y * X + X * Y * Y -
      Y * X * X + Y * X * Y + Y * Y * X - Y * Y * Y := by noncomm_ring
  rw [e, hXYX, hYXY]
  have h1 : X * X * X = X := by rw [hX, hX]
  have h2 : X * X * Y = X * Y := by rw [hX]
  have h3 : X * Y * Y = X * Y := by rw [mul_assoc, hY]
  have h4 : Y * X * X = Y * X := by rw [mul_assoc, hX]
  have h5 : Y * Y * X = Y * X := by rw [hY]
  have h6 : Y * Y * Y = Y := by rw [hY, hY]
  rw [h1, h2, h3, h4, h5, h6, sub_smul, one_smul, smul_sub]
  abel

lemma tn_pure_diff (x y : n → ℂ) (hx : star x ⬝ᵥ x = 1) (hy : star y ⬝ᵥ y = 1) :
    traceNorm (vecMulVec x (star x) - vecMulVec y (star y)) ≤
      2 * Real.sqrt (1 - Complex.normSq (star x ⬝ᵥ y)) := by
  set X := vecMulVec x (star x)
  set Y := vecMulVec y (star y)
  set c := star x ⬝ᵥ y with hcdef
  have hc' : star y ⬝ᵥ x = star c := by
    rw [hcdef, ← Matrix.star_dotProduct_star, star_star]
  have hXX : X * X = X := by rw [vmv_mul, hx, one_smul]
  have hYY : Y * Y = Y := by rw [vmv_mul, hy, one_smul]
  have hk : c * star c = ((Complex.normSq c : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  have hXYX : X * Y * X = ((Complex.normSq c : ℝ) : ℂ) • X := by
    simp only [X, Y]
    rw [vmv_mul, Matrix.smul_mul, vmv_mul, smul_smul, ← hcdef, hc', hk]
  have hYXY : Y * X * Y = ((Complex.normSq c : ℝ) : ℂ) • Y := by
    simp only [X, Y]
    rw [vmv_mul, Matrix.smul_mul, vmv_mul, smul_smul, hc', ← hcdef, mul_comm, hk]
  set M := X - Y with hM
  set κ : ℝ := 1 - Complex.normSq c with hκ
  have h3 : M * M * M = (κ : ℂ) • M := by
    rw [hM, cube_lemma X Y _ hXX hYY hXYX hYXY, hκ]; push_cast; rfl
  have hXh : Xᴴ = X := by
    simp only [X]; rw [Matrix.conjTranspose_vecMulVec]; simp
  have hYh : Yᴴ = Y := by
    simp only [Y]; rw [Matrix.conjTranspose_vecMulVec]; simp
  have hMh : Mᴴ = M := by rw [hM, Matrix.conjTranspose_sub, hXh, hYh]
  have hMM : (M * M).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self M; rwa [hMh] at this
  have htrX : X.trace = 1 := by
    simp only [X]; rw [Matrix.trace_vecMulVec]; rw [← hx]; simp [dotProduct, mul_comm]
  have htrY : Y.trace = 1 := by
    simp only [Y]; rw [Matrix.trace_vecMulVec]; rw [← hy]; simp [dotProduct, mul_comm]
  have htrXY : (X * Y).trace = ((Complex.normSq c : ℝ) : ℂ) := by
    simp only [X, Y]
    rw [vmv_mul, Matrix.trace_smul, Matrix.trace_vecMulVec, ← hcdef, smul_eq_mul, ← hk]
    congr 1
    rw [hcdef, ← Matrix.star_dotProduct_star]
    simp [dotProduct, mul_comm]
  have htrYX : (Y * X).trace = ((Complex.normSq c : ℝ) : ℂ) := by
    rw [Matrix.trace_mul_comm, htrXY]
  have htrMM : (M * M).trace = ((2 * κ : ℝ) : ℂ) := by
    rw [hM, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hXX, hYY, Matrix.trace_sub,
      Matrix.trace_sub, Matrix.trace_sub, htrX, htrY, htrXY, htrYX, hκ]
    push_cast; ring
  have hκ0 : 0 ≤ κ := by
    have := (Complex.nonneg_iff.1 hMM.trace_nonneg).1
    rw [htrMM] at this; simp at this; linarith
  unfold traceNorm
  rw [hMh]
  rcases hκ0.lt_or_eq with hpos | hzero
  · set Q : Matrix n n ℂ := (((Real.sqrt κ)⁻¹ : ℝ) : ℂ) • (M * M) with hQ
    have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hpos
    have hQp : Q.PosSemidef := hMM.smul (Complex.zero_le_real.2 (by positivity))
    have hQQ : Q * Q = M * M := by
      rw [hQ, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [show M * M * (M * M) = M * (M * M * M) by simp [Matrix.mul_assoc], h3, Matrix.mul_smul,
        smul_smul]
      rw [show ((((Real.sqrt κ)⁻¹ : ℝ) : ℂ) * (((Real.sqrt κ)⁻¹ : ℝ) : ℂ)) * (κ : ℂ) = 1 by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← mul_inv,
          Real.mul_self_sqrt hκ0, inv_mul_cancel₀ hpos.ne']; simp]
      rw [one_smul]
    rw [← hQQ, g55b_sqrt_sq hQp, hQ, Matrix.trace_smul, htrMM, smul_eq_mul, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    have : (Real.sqrt κ)⁻¹ * (2 * κ) = 2 * Real.sqrt κ := by
      field_simp; rw [Real.sq_sqrt hκ0]
    rw [this]
  · have h0 : M * M * M = 0 := by rw [h3, ← hzero]; simp
    have hz : M * M = 0 := by
      have : (M * M)ᴴ * (M * M) = 0 := by
        rw [Matrix.conjTranspose_mul, hMh, show M * M * (M * M) = M * (M * M * M) by
          simp [Matrix.mul_assoc], h0, Matrix.mul_zero]
      exact Matrix.conjTranspose_mul_self_eq_zero.1 this
    rw [hz, ← hzero]; simp

end S64FC

namespace S64FC
open G55BF Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma kraus_term {m : ℕ} (E : Fin m → Matrix n n ℂ) (ψ : n → ℂ) :
    krausApply E (vecMulVec ψ (star ψ)) = ∑ j, vecMulVec (E j *ᵥ ψ) (star (E j *ᵥ ψ)) := by
  unfold krausApply
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

lemma kraus_f {m : ℕ} (E : Fin m → Matrix n n ℂ) (ψ : n → ℂ) :
    (vecMulVec ψ (star ψ) * krausApply E (vecMulVec ψ (star ψ))).trace.re =
      ∑ j, Complex.normSq (star ψ ⬝ᵥ (E j *ᵥ ψ)) := by
  rw [kraus_term, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [vmv_mul, Matrix.trace_smul, smul_eq_mul]
  have : (vecMulVec ψ (star (E j *ᵥ ψ))).trace = star (star ψ ⬝ᵥ (E j *ᵥ ψ)) := by
    rw [Matrix.trace_vecMulVec, ← Matrix.star_dotProduct_star, star_star]
    simp [dotProduct, mul_comm]
  rw [this, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

lemma traceRight_sub {m : Type*} [Fintype m] (A B : Matrix (n × m) (n × m) ℂ) :
    traceRight (A - B) = traceRight A - traceRight B := by
  ext a b; simp [traceRight, Finset.sum_sub_distrib]

lemma kraus_pure [Nonempty n] {m : ℕ} (E : Fin m → Matrix n n ℂ) (hE : ∑ j, (E j)ᴴ * E j = 1)
    (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    traceNorm (krausApply E (vecMulVec ψ (star ψ)) - vecMulVec ψ (star ψ)) ≤
      2 * Real.sqrt (1 - (vecMulVec ψ (star ψ) * krausApply E (vecMulVec ψ (star ψ))).trace.re) := by
  rw [kraus_f]
  set φ : Fin m → n → ℂ := fun j => E j *ᵥ ψ with hφ
  set g : Fin m → ℂ := fun j => star ψ ⬝ᵥ φ j with hg
  set f' : ℝ := ∑ j, Complex.normSq (g j) with hf'
  set Φ : n × Fin m → ℂ := fun z => φ z.2 z.1 with hΦ
  have hσ : krausApply E (vecMulVec ψ (star ψ)) = traceRight (vecMulVec Φ (star Φ)) := by
    rw [kraus_term]
    ext a b
    simp [traceRight, vecMulVec_apply, Φ, φ, Matrix.sum_apply]
  have hΦn : star Φ ⬝ᵥ Φ = 1 := by
    have e1 : star Φ ⬝ᵥ Φ = ∑ j, star (φ j) ⬝ᵥ φ j := by
      simp only [dotProduct, Φ, Pi.star_apply, Fintype.sum_prod_type]
      exact Finset.sum_comm
    have e2 : ∀ j, star (φ j) ⬝ᵥ φ j = star ψ ⬝ᵥ (((E j)ᴴ * E j) *ᵥ ψ) := by
      intro j
      simp only [φ]
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    rw [e1]
    simp only [e2]
    rw [← dotProduct_sum, ← Matrix.sum_mulVec, hE, Matrix.one_mulVec, hψ]
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp at hE
    · exact h
  have hf0 : 0 ≤ f' := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  set α : Fin m → ℂ := if f' = 0 then Pi.single ⟨0, hm⟩ 1
    else fun j => g j / ((Real.sqrt f' : ℝ) : ℂ) with hα
  have hαn : star α ⬝ᵥ α = 1 := by
    by_cases h : f' = 0
    · simp [hα, h, dotProduct, Pi.single_apply]
    · have hp : 0 < f' := lt_of_le_of_ne hf0 (Ne.symm h)
      have hs : ((Real.sqrt f' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hp).ne'
      simp only [hα, h, if_false, dotProduct, Pi.star_apply, star_div₀]
      have : ∀ j, star (g j / ((Real.sqrt f' : ℝ) : ℂ)) * (g j / ((Real.sqrt f' : ℝ) : ℂ)) =
          ((Complex.normSq (g j) / f' : ℝ) : ℂ) := by
        intro j
        rw [star_div₀, Complex.star_def, Complex.conj_ofReal, div_mul_div_comm, mul_comm,
          Complex.mul_conj, ← Complex.ofReal_mul, Real.mul_self_sqrt hf0]
        push_cast; ring
      simp only [star_div₀] at this
      rw [Finset.sum_congr rfl fun j _ => this j, ← Complex.ofReal_sum, ← Finset.sum_div,
        div_self h]
      simp
  set Ψ : n × Fin m → ℂ := fun z => ψ z.1 * α z.2 with hΨ
  have hΨtr : traceRight (vecMulVec Ψ (star Ψ)) = vecMulVec ψ (star ψ) := by
    ext a b
    simp only [traceRight, vecMulVec_apply, Ψ, Pi.star_apply, Matrix.of_apply, star_mul]
    have : ∑ j, ψ a * α j * (star (α j) * star (ψ b)) = ψ a * star (ψ b) * (star α ⬝ᵥ α) := by
      rw [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.star_apply]; ring
    rw [this, hαn, mul_one]
  have hΨn : star Ψ ⬝ᵥ Ψ = 1 := by
    have : star Ψ ⬝ᵥ Ψ = (star ψ ⬝ᵥ ψ) * (star α ⬝ᵥ α) := by
      simp only [dotProduct, Ψ, Pi.star_apply, star_mul, Fintype.sum_prod_type, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, hψ, hαn, one_mul]
  have hov : Complex.normSq (star Φ ⬝ᵥ Ψ) = f' := by
    have e : star Φ ⬝ᵥ Ψ = ∑ j, star (g j) * α j := by
      simp only [dotProduct, Φ, Ψ, Pi.star_apply, Fintype.sum_prod_type, g, φ]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [star_mul, star_star, Pi.star_apply]; ring
    rw [e]
    by_cases h : f' = 0
    · have hz : ∀ j, g j = 0 := by
        intro j
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (g j))).1 h j
          (Finset.mem_univ _)
        exact Complex.normSq_eq_zero.1 this
      simp [hz, h]
    · have hp : 0 < f' := lt_of_le_of_ne hf0 (Ne.symm h)
      have : ∑ j, star (g j) * α j = ((Real.sqrt f' : ℝ) : ℂ) := by
        simp only [hα, h, if_false]
        have hs : ((Real.sqrt f' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hp).ne'
        have : ∀ j, star (g j) * (g j / ((Real.sqrt f' : ℝ) : ℂ)) =
            ((Complex.normSq (g j) : ℝ) : ℂ) / ((Real.sqrt f' : ℝ) : ℂ) := by
          intro j
          rw [mul_div_assoc', mul_comm, Complex.star_def, Complex.mul_conj]
        rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.sum_div, ← Complex.ofReal_sum,
          ← hf']
        rw [div_eq_iff hs, ← Complex.ofReal_mul, Real.mul_self_sqrt hf0]
      rw [this, Complex.normSq_ofReal, Real.mul_self_sqrt hf0]
  have key := tn_pure_diff Φ Ψ hΦn hΨn
  rw [hov] at key
  rw [hσ, ← hΨtr, ← traceRight_sub]
  exact (tn_traceRight_le _).trans key

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

def Lmap {m : ℕ} (E : Fin m → Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := krausApply E X - X
  map_add' X Y := by
    simp only [krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]; abel
  map_smul' c X := by
    simp only [krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, smul_sub,
      RingHom.id_apply]

lemma Lmap_apply {m : ℕ} (E : Fin m → Matrix n n ℂ) (X : Matrix n n ℂ) :
    Lmap E X = krausApply E X - X := rfl

variable [Nonempty n] {m : ℕ} (E : Fin m → Matrix n n ℂ) (hE : ∑ j, (E j)ᴴ * E j = 1) (s : ℝ)
  (hs : ∀ ψ : n → ℂ, star ψ ⬝ᵥ ψ = 1 →
    Real.sqrt (1 - (vecMulVec ψ (star ψ) * krausApply E (vecMulVec ψ (star ψ))).trace.re) ≤ s)
include hE hs

lemma bound_vv (v : n → ℂ) :
    traceNorm (Lmap E (vecMulVec v (star v))) ≤ 2 * s * (star v ⬝ᵥ v).re := by
  set r := (star v ⬝ᵥ v).re with hr
  have hr0 : 0 ≤ r := dot_star_re_nonneg v
  rcases hr0.lt_or_eq with hrp | hrz
  · set c : ℝ := (Real.sqrt r)⁻¹
    have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hrp
    set ψ : n → ℂ := (c : ℂ) • v with hψdef
    have hψ : star ψ ⬝ᵥ ψ = 1 := by
      rw [hψdef, star_smul, smul_dotProduct, dotProduct_smul, dot_star_real v, ← hr]
      simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal, RCLike.star_def]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      have : c * (c * r) = 1 := by
        simp only [c]; rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hr0, inv_mul_cancel₀ hrp.ne']
      rw [this]; simp
    have hvv : vecMulVec v (star v) = (r : ℂ) • vecMulVec ψ (star ψ) := by
      ext a b
      simp only [vecMulVec_apply, Matrix.smul_apply, hψdef, Pi.smul_apply, Pi.star_apply,
        smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal]
      have : (r : ℂ) * ((c : ℂ) * (c : ℂ)) = 1 := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
        simp only [c]; rw [← mul_inv, Real.mul_self_sqrt hr0, mul_inv_cancel₀ hrp.ne']; simp
      linear_combination (-(v a * (starRingEnd ℂ) (v b))) * this
    rw [hvv, map_smul]
    calc traceNorm ((r : ℂ) • Lmap E (vecMulVec ψ (star ψ)))
        ≤ ‖(r : ℂ)‖ * traceNorm (Lmap E (vecMulVec ψ (star ψ))) := tn_smul_le _ _
      _ ≤ r * (2 * s) := by
          rw [Complex.norm_real, Real.norm_of_nonneg hr0]
          apply mul_le_mul_of_nonneg_left _ hr0
          rw [Lmap_apply]
          exact (kraus_pure E hE ψ hψ).trans (by linarith [hs ψ hψ])
      _ = 2 * s * r := by ring
  · have hv : v = 0 := by
      have h0 : star v ⬝ᵥ v = 0 := by rw [dot_star_real v, ← hr, ← hrz]; simp
      exact dotProduct_star_self_eq_zero.1 h0
    subst hv
    rw [← hrz]; simp [tn_zero]

lemma bound_ab (a b : n → ℂ) :
    traceNorm (Lmap E (vecMulVec a (star b))) ≤
      2 * s * ((star a ⬝ᵥ a).re + (star b ⬝ᵥ b).re) := by
  set w : Fin 4 → n → ℂ := fun k => a + (Complex.I ^ (k : ℕ)) • b with hw
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  have hpol : vecMulVec a (star b) =
      ∑ k : Fin 4, ((1/4 : ℂ) * Complex.I ^ (k : ℕ)) • vecMulVec (w k) (star (w k)) := by
    ext x y
    simp only [Fin.sum_univ_four, hw, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
      Pi.add_apply, Pi.smul_apply, Pi.star_apply, star_add, star_smul, smul_eq_mul,
      Fin.val_zero, Fin.val_one, Fin.val_two, Matrix.sum_apply,
      show ((3 : Fin 4) : ℕ) = 3 from rfl, pow_zero, pow_one, hI2, hI3, Complex.star_def,
      map_neg, Complex.conj_I, map_one, RCLike.star_def]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hsum : ∑ k : Fin 4, (star (w k) ⬝ᵥ w k).re = 4 * ((star a ⬝ᵥ a).re + (star b ⬝ᵥ b).re) := by
    simp only [Fin.sum_univ_four, hw, star_add, star_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, Fin.val_zero, Fin.val_one, Fin.val_two,
      show ((3 : Fin 4) : ℕ) = 3 from rfl, pow_zero, pow_one, hI2, hI3, Complex.star_def,
      map_neg, Complex.conj_I, map_one, RCLike.star_def]
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [hpol, map_sum]
  refine (tn_sum_le _ _).trans ?_
  calc ∑ k : Fin 4, traceNorm (Lmap E (((1/4 : ℂ) * Complex.I ^ (k : ℕ)) •
        vecMulVec (w k) (star (w k))))
      ≤ ∑ k : Fin 4, (1/4) * (2 * s * (star (w k) ⬝ᵥ w k).re) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [map_smul]
        refine (tn_smul_le _ _).trans ?_
        have hn : ‖(1/4 : ℂ) * Complex.I ^ (k : ℕ)‖ = 1/4 := by
          rw [norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one]; norm_num
        rw [hn]
        exact mul_le_mul_of_nonneg_left (bound_vv E hE s hs (w k)) (by norm_num)
    _ = 2 * s * ((star a ⬝ᵥ a).re + (star b ⬝ᵥ b).re) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, hsum]; ring

lemma bound_X (X : Matrix n n ℂ) : traceNorm (Lmap E X) ≤ 4 * s * traceNorm X := by
  obtain ⟨W, hW, hX⟩ := g55b_polar X
  set P := cfc Real.sqrt (Xᴴ * X) with hP
  have hPp : P.PosSemidef := g55b_sqrt_psd _
  set sP := cfc Real.sqrt P with hsPdef
  have hsh : sPᴴ = sP := (g55b_sqrt_psd P).1.eq
  have hss : sP * sP = P := G55BF.sqrt_mul_sqrt hPp
  set A := W * sP with hA
  have hdec : X = ∑ j, vecMulVec (fun i => A i j) (star (fun i => sP i j)) := by
    ext x y
    rw [Matrix.sum_apply]
    simp only [vecMulVec_apply, Pi.star_apply]
    have : ∀ j, star (sP y j) = sP j y := by
      intro j
      have := congrFun (congrFun hsh j) y
      rwa [Matrix.conjTranspose_apply] at this
    simp only [this]
    rw [hX, ← hss, ← Matrix.mul_assoc, Matrix.mul_apply]
  have hna : ∀ j, (star (fun i => A i j) ⬝ᵥ (fun i => A i j)).re = (P j j).re := by
    intro j
    have : star (fun i => A i j) ⬝ᵥ (fun i => A i j) = (Aᴴ * A) j j := by
      simp [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [this, hA, Matrix.conjTranspose_mul, hsh,
      show sP * Wᴴ * (W * sP) = sP * (Wᴴ * W) * sP by simp [Matrix.mul_assoc], hW,
      Matrix.mul_one, hss]
  have hnb : ∀ j, (star (fun i => sP i j) ⬝ᵥ (fun i => sP i j)).re = (P j j).re := by
    intro j
    have : star (fun i => sP i j) ⬝ᵥ (fun i => sP i j) = (sPᴴ * sP) j j := by
      simp [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [this, hsh, hss]
  conv_lhs => rw [hdec, map_sum]
  refine (tn_sum_le _ _).trans ?_
  calc ∑ j, traceNorm (Lmap E (vecMulVec (fun i => A i j) (star (fun i => sP i j))))
      ≤ ∑ j, 2 * s * ((P j j).re + (P j j).re) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have := bound_ab E hE s hs (fun i => A i j) (fun i => sP i j)
        rwa [hna, hnb] at this
    _ = 4 * s * traceNorm X := by
        unfold traceNorm
        rw [← hP, Matrix.trace, Complex.re_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Matrix.diag]; ring

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

lemma kraus_tn_bound {N' : Type*} [Fintype N'] [DecidableEq N'] {r : ℕ}
    (L : Fin r → Matrix N' N ℂ) (lam : ℝ)
    (hQ : ∀ w : N → ℂ, ∑ m, (star (L m *ᵥ w) ⬝ᵥ (L m *ᵥ w)).re ≤ lam * (star w ⬝ᵥ w).re)
    (X : Matrix N N ℂ) :
    traceNorm (∑ m, L m * X * (L m)ᴴ) ≤ lam * traceNorm X := by
  obtain ⟨a, b, hX, ha, hb⟩ := rank_one_dec X
  have e : ∑ m, L m * X * (L m)ᴴ =
      ∑ j, ∑ m, vecMulVec (L m *ᵥ a j) (star (L m *ᵥ b j)) := by
    rw [hX, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]
  rw [e]
  refine (tn_sum_le _ _).trans ?_
  calc ∑ j, traceNorm (∑ m, vecMulVec (L m *ᵥ a j) (star (L m *ᵥ b j)))
      ≤ ∑ j, ∑ m, ((star (L m *ᵥ a j) ⬝ᵥ (L m *ᵥ a j)).re +
          (star (L m *ᵥ b j) ⬝ᵥ (L m *ᵥ b j)).re) / 2 :=
        Finset.sum_le_sum fun j _ => (tn_sum_le _ _).trans
          (Finset.sum_le_sum fun m _ => tn_rank1 _ _)
    _ ≤ ∑ j, lam * ((star (a j) ⬝ᵥ a j).re + (star (b j) ⬝ᵥ b j).re) / 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← Finset.sum_div, Finset.sum_add_distrib]
        have h1 := hQ (a j)
        have h2 := hQ (b j)
        rw [mul_add]
        linarith
    _ = lam * traceNorm X := by
        rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib, ha, hb]; ring

lemma top_eigen [Nonempty N] {P : Matrix N N ℂ} (hP : P.PosSemidef) :
    ∃ v : N → ℂ, star v ⬝ᵥ v = 1 ∧ ∃ lam : ℝ, 0 ≤ lam ∧ P *ᵥ v = (lam : ℂ) • v ∧
      ((lam : ℂ) • (1 : Matrix N N ℂ) - P).PosSemidef := by
  have hH := hP.1
  obtain ⟨i0, hi0⟩ := Finite.exists_max hH.eigenvalues
  set lam := hH.eigenvalues i0
  refine ⟨⇑(hH.eigenvectorBasis i0), ?_, lam, hP.eigenvalues_nonneg i0, ?_, ?_⟩
  · have h1 := (hH.eigenvectorBasis).orthonormal.1 i0
    have h2 : ‖hH.eigenvectorBasis i0‖ ^ 2 = 1 := by rw [h1]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h2
    rw [dot_star_real]
    have : (star ⇑(hH.eigenvectorBasis i0) ⬝ᵥ ⇑(hH.eigenvectorBasis i0)).re = 1 := by
      rw [← h2]
      simp only [dotProduct, Complex.re_sum, Pi.star_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    rw [this]; simp
  · rw [hH.mulVec_eigenvectorBasis i0]
    ext k; simp [RCLike.real_smul_eq_coe_smul (K := ℂ), lam]
  · have e : (lam : ℂ) • (1 : Matrix N N ℂ) - P = cfc (fun t : ℝ => lam - t) P := by
      rw [cfc_sub (fun _ => lam) (fun t => t) P, cfc_const lam P, cfc_id' ℝ P]
      simp [Algebra.algebraMap_eq_smul_one]
    rw [e, ← Matrix.nonneg_iff_posSemidef]
    apply cfc_nonneg
    intro t ht
    rw [hH.spectrum_real_eq_range_eigenvalues] at ht
    obtain ⟨i, rfl⟩ := ht
    linarith [hi0 i]

end S64T6

section
open scoped Matrix.Norms.L2Operator

lemma eig_le_spec {N : Type*} [Fintype N] [DecidableEq N] {D : Matrix N N ℂ} (hD : D.IsHermitian)
    (i : N) : |hD.eigenvalues i| ≤ specNorm D := by
  have h := Matrix.l2_opNorm_mulVec D (hD.eigenvectorBasis i)
  rw [hD.mulVec_eigenvectorBasis i] at h
  have h1 : ‖hD.eigenvectorBasis i‖ = 1 := (hD.eigenvectorBasis).orthonormal.1 i
  have e : (EuclideanSpace.equiv N ℂ).symm (hD.eigenvalues i • ⇑(hD.eigenvectorBasis i)) =
      (hD.eigenvalues i : ℂ) • hD.eigenvectorBasis i := by
    ext k
    change hD.eigenvalues i • (hD.eigenvectorBasis i) k = (hD.eigenvalues i : ℂ) * (hD.eigenvectorBasis i) k
    rw [Complex.real_smul]
  rw [e, norm_smul, h1, mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end

lemma abs_le_spec {N : Type*} [Fintype N] [DecidableEq N] {D : Matrix N N ℂ} (hD : D.IsHermitian) :
    ((specNorm D : ℂ) • (1 : Matrix N N ℂ) - cfc (fun t : ℝ => |t|) D).PosSemidef := by
  have e : (specNorm D : ℂ) • (1 : Matrix N N ℂ) - cfc (fun t : ℝ => |t|) D =
      cfc (fun t : ℝ => specNorm D - |t|) D := by
    rw [cfc_sub (fun _ => specNorm D) (fun t => |t|) D, cfc_const (specNorm D) D]
    simp [Algebra.algebraMap_eq_smul_one]
  rw [e, ← Matrix.nonneg_iff_posSemidef]
  apply cfc_nonneg
  intro t ht
  rw [hD.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  linarith [eig_le_spec hD i]
end

noncomputable section
open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker
open Filter Set

namespace S64P50
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P50
open S64FC S64FC2 S64T6 Matrix

lemma arn_apply {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (T : M r) (X : M dx) (y z : Fin dy) :
    arnFamily V T X y z = ∑ a, ∑ b, (∑ k, ∑ l, T k l * V k y a * conj (V l z b)) * X a b := rfl

lemma comp_apply {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (X : M dx) (k l : Fin r) :
    complementaryMap V X k l = ∑ a, ∑ b, (∑ y, V k y a * conj (V l y b)) * X a b := rfl

lemma sum4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ k, ∑ l, f a b k l = ∑ l, ∑ b, ∑ a, ∑ k, f a b k l := by
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm,
    Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_comm

lemma cl1a {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (T : M r) (X : M dx) :
      arnFamily V T X = traceRight
        (((1 : M dy) ⊗ₖ T.transpose) * stinespringOperator V * X * (stinespringOperator V)ᴴ) := by
  ext y z
  rw [arn_apply]
  simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.transpose_apply, stinespringOperator, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_mul, Finset.mul_sum, RCLike.star_def]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sum4]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma sum5 {Y A B K L : Type} [Fintype Y] [Fintype A] [Fintype B] [Fintype K] [Fintype L]
    (f : Y → A → B → K → L → ℂ) :
    ∑ y, ∑ a, ∑ b, ∑ k, ∑ l, f y a b k l = ∑ l, ∑ k, ∑ a, ∑ b, ∑ y, f y a b k l := by
  simp only [← Finset.sum_product']
  exact Fintype.sum_equiv (Equiv.mk (fun p => ⟨p.2.2.2.2, p.2.2.2.1, p.2.1, p.2.2.1, p.1⟩)
    (fun q => ⟨q.2.2.2.2, q.2.2.1, q.2.2.2.1, q.2.1, q.1⟩) (fun _ => rfl) (fun _ => rfl)) _ _
    (fun _ => rfl)

lemma cl1b {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (T : M r) (X : M dx) :
    (arnFamily V T X).trace = (T.transpose * complementaryMap V X).trace := by
  simp only [Matrix.trace, Matrix.diag, arn_apply, Matrix.mul_apply, Matrix.transpose_apply,
    comp_apply, Finset.mul_sum, Finset.sum_mul]
  rw [sum5]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl
    fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma hs_arn {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (T : M r) (hT : T.IsHermitian)
    (a b : Fin dx) :
    hilbertSchmidtAdjoint (arnFamily V T) 1 a b =
      ∑ y, ∑ k, ∑ l, conj (V k y a) * T l k * V l y b := by
  simp only [hilbertSchmidtAdjoint, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, arn_apply, Matrix.single_apply, ite_and]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, map_sum, map_mul, Complex.conj_conj]
  simp only [apply_ite (starRingEnd ℂ), map_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, map_mul, Complex.conj_conj]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl
    fun l _ => ?_
  have := hT.apply l k
  rw [show (starRingEnd ℂ) (T k l) = T l k from this]
  ring

lemma cl2 {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (T : M r) (hT : T.IsHermitian) :
    hilbertSchmidtAdjoint (arnFamily V T) 1 =
      (stinespringOperator V)ᴴ * ((1 : M dy) ⊗ₖ T.transpose) * stinespringOperator V := by
  ext a b
  rw [hs_arn V T hT]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, stinespringOperator,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
    RCLike.star_def, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_comm

lemma cl3 {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (T : M r) (hT : T.IsHermitian) :
    hilbertSchmidtAdjoint (arnFamily V T) 1 =
      hilbertSchmidtAdjoint (complementaryMap V) T.transpose := by
  ext a b
  rw [hs_arn V T hT]
  simp only [hilbertSchmidtAdjoint, comp_apply, Matrix.single_apply, ite_and, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    apply_ite (starRingEnd ℂ), map_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, map_sum,
    map_mul, Complex.conj_conj, Matrix.transpose_apply]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun y _ => by ring

lemma sum5m {A B K L Mm : Type} [Fintype A] [Fintype B] [Fintype K] [Fintype L] [Fintype Mm]
    (f : A → B → K → L → Mm → ℂ) :
    ∑ a, ∑ b, ∑ k, ∑ l, ∑ m, f a b k l m = ∑ m, ∑ a, ∑ b, ∑ k, ∑ l, f a b k l m := by
  simp only [← Finset.sum_product']
  exact Fintype.sum_equiv (Equiv.mk (fun p => ⟨p.2.2.2.2, p.1, p.2.1, p.2.2.1, p.2.2.2.1⟩)
    (fun q => ⟨q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2, q.1⟩) (fun _ => rfl) (fun _ => rfl)) _ _
    (fun _ => rfl)

lemma sum4p {A B K L : Type} [Fintype A] [Fintype B] [Fintype K] [Fintype L]
    (f : A → B → K → L → ℂ) :
    ∑ a, ∑ b, ∑ k, ∑ l, f a b k l = ∑ b, ∑ l, ∑ a, ∑ k, f a b k l := by
  simp only [← Finset.sum_product']
  exact Fintype.sum_equiv (Equiv.mk (fun p => ⟨p.2.1, p.2.2.2, p.1, p.2.2.1⟩)
    (fun q => ⟨q.2.2.1, q.1, q.2.2.2, q.2.1⟩) (fun _ => rfl) (fun _ => rfl)) _ _
    (fun _ => rfl)

/-- Kraus operators of Ψ_T for T = B Bᴴ. -/
def krausOf {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (B : M r) (m : Fin r) :
    Matrix (Fin dy) (Fin dx) ℂ := ∑ k, B k m • V k

lemma kraus_rep {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (T B : M r)
    (hB : T = B * Bᴴ) (X : M dx) :
    arnFamily V T X = ∑ m, krausOf V B m * X * (krausOf V B m)ᴴ := by
  ext y z
  rw [arn_apply, Matrix.sum_apply]
  simp only [hB, krausOf, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, star_sum, star_mul', RCLike.star_def, Finset.sum_mul,
    Finset.mul_sum]
  rw [sum5m]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [sum4p]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl
    fun a _ => Finset.sum_congr rfl fun k _ => by ring

lemma amp_kraus {n ι κ : Type} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ] {r : ℕ}
    (Φ : Matrix ι ι ℂ → Matrix κ κ ℂ) (K : Fin r → Matrix κ ι ℂ)
    (hΦ : ∀ X, Φ X = ∑ m, K m * X * (K m)ᴴ) (X : Matrix (n × ι) (n × ι) ℂ) :
    idTensorSuperop Φ X = ∑ m, ((1 : Matrix n n ℂ) ⊗ₖ K m) * X * ((1 : Matrix n n ℂ) ⊗ₖ K m)ᴴ := by
  ext ⟨p1, p2⟩ ⟨q1, q2⟩
  simp only [idTensorSuperop, Matrix.of_apply, hΦ, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [apply_ite star, star_zero, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma cp_kraus {ι κ : Type} [Fintype ι] [Fintype κ] {r : ℕ}
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (K : Fin r → Matrix κ ι ℂ)
    (hΦ : ∀ X, Φ X = ∑ m, K m * X * (K m)ᴴ) : Entanglement.IsCompletelyPositive Φ := by
  intro n X hX
  rw [amp_kraus (fun X => Φ X) K hΦ X]
  exact Matrix.posSemidef_sum _ fun m _ => hX.mul_mul_conjTranspose_same _

lemma cp_arn {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (T B : M r)
    (hB : T = B * Bᴴ) : Entanglement.IsCompletelyPositive (arnFamily V T) :=
  cp_kraus _ (krausOf V B) (kraus_rep V T B hB)

lemma arn_sub {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (A B : M r) :
    arnFamily V (A - B) = arnFamily V A - arnFamily V B := by
  apply LinearMap.ext; intro X; ext y z
  simp only [LinearMap.sub_apply, Matrix.sub_apply, arn_apply, Matrix.sub_apply, sub_mul,
    Finset.sum_sub_distrib]

lemma arn_sum {dx dy r n : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (A : Fin n → M r) :
    arnFamily V (∑ i, A i) = ∑ i, arnFamily V (A i) := by
  apply LinearMap.ext; intro X; ext y z
  simp only [LinearMap.sum_apply, Matrix.sum_apply, arn_apply, Finset.sum_mul]
  rw [sum5m]


section
open scoped MatrixOrder
lemma schatten_one {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) :
    schattenNorm 1 A = traceNorm A := by
  unfold schattenNorm traceNorm
  rw [if_neg ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one, div_one]
  rw [show ∀ x : ℝ, Real.rpow x 1 = x from fun x => Real.rpow_one x]
  congr 2
  apply cfc_congr
  intro t ht
  have hnn : (0 : Matrix I I ℂ) ≤ Aᴴ * A :=
    Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self A)
  have : 0 ≤ t := spectrum_nonneg_of_nonneg hnn ht
  rw [Real.sqrt_eq_rpow]; rfl
end

lemma psd_sqrt_fac {r : ℕ} {T : M r} (hT : T.PosSemidef) :
    T = cfc Real.sqrt T * (cfc Real.sqrt T)ᴴ := by
  rw [(g55b_sqrt_psd T).1.eq, G55BF.sqrt_mul_sqrt hT]

lemma cp_psd {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) {T : M r}
    (hT : T.PosSemidef) : Entanglement.IsCompletelyPositive (arnFamily V T) :=
  cp_arn V T _ (psd_sqrt_fac hT)

lemma quad_P {dx dy r : ℕ} (K : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (u : Fin dx → ℂ) :
    ∑ m, star (K m *ᵥ u) ⬝ᵥ (K m *ᵥ u) = star u ⬝ᵥ ((∑ m, (K m)ᴴ * K m) *ᵥ u) := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

lemma quad_L {dx dy r n : ℕ} (K : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (lam : ℝ)
    (hq : ∀ u : Fin dx → ℂ, ∑ m, (star (K m *ᵥ u) ⬝ᵥ (K m *ᵥ u)).re ≤ lam * (star u ⬝ᵥ u).re)
    (w : Fin n × Fin dx → ℂ) :
    ∑ m, (star (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ K m) *ᵥ w) ⬝ᵥ
      (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ K m) *ᵥ w)).re ≤ lam * (star w ⬝ᵥ w).re := by
  have hL : ∀ m (i : Fin n) (y : Fin dy), (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ K m) *ᵥ w) (i, y) =
      (K m *ᵥ fun a => w (i, a)) y := by
    intro m i y
    simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have e1 : ∀ m, star (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ K m) *ᵥ w) ⬝ᵥ
      (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ K m) *ᵥ w) =
      ∑ i, star (K m *ᵥ fun a => w (i, a)) ⬝ᵥ (K m *ᵥ fun a => w (i, a)) := by
    intro m
    simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, hL]
  have e2 : star w ⬝ᵥ w = ∑ i, star (fun a => w (i, a)) ⬝ᵥ (fun a => w (i, a)) := by
    simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply]
  simp only [e1, Complex.re_sum]
  rw [Finset.sum_comm, e2, Complex.re_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hq (fun a => w (i, a))

lemma tr_sum_kraus {dx dy r : ℕ} (K : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (X : M dx) :
    (∑ m, K m * X * (K m)ᴴ).trace = ((∑ m, (K m)ᴴ * K m) * X).trace := by
  rw [Matrix.trace_sum, Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]

lemma psd_kraus_sum {I J : Type*} [Fintype I] [Fintype J] {r : ℕ} (K : Fin r → Matrix J I ℂ)
    {X : Matrix I I ℂ} (hX : X.PosSemidef) : (∑ m, K m * X * (K m)ᴴ).PosSemidef :=
  Matrix.posSemidef_sum _ fun m _ => hX.mul_mul_conjTranspose_same _

lemma cl6 {dx dy r : ℕ} (hdx : 0 < dx) (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (T : M r)
    (hT : T.PosSemidef) :
    inducedNorm 1 (arnFamily V T) = cbTraceNorm (arnFamily V T) ∧
      ∃ rho : M dx, IsDensityMatrix rho ∧
        cbTraceNorm (arnFamily V T) = (T.transpose * complementaryMap V rho).trace.re ∧
        ∀ tau : M dx, IsDensityMatrix tau →
          (T.transpose * complementaryMap V tau).trace.re ≤
            (T.transpose * complementaryMap V rho).trace.re := by
  set B := cfc Real.sqrt T
  set K := krausOf V B
  have hrep : ∀ X, arnFamily V T X = ∑ m, K m * X * (K m)ᴴ := kraus_rep V T B (psd_sqrt_fac hT)
  set P := ∑ m, (K m)ᴴ * K m with hPdef
  have hPp : P.PosSemidef :=
    Matrix.posSemidef_sum _ fun m _ => Matrix.posSemidef_conjTranspose_mul_self _
  have : Nonempty (Fin dx) := ⟨⟨0, hdx⟩⟩
  obtain ⟨v, hv, lam, hlam0, hPv, hLP⟩ := top_eigen hPp
  have hq : ∀ u : Fin dx → ℂ, ∑ m, (star (K m *ᵥ u) ⬝ᵥ (K m *ᵥ u)).re ≤ lam * (star u ⬝ᵥ u).re := by
    intro u
    rw [← Complex.re_sum, quad_P]
    have h := (Complex.nonneg_iff.1 (hLP.dotProduct_mulVec_nonneg u)).1
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul] at h
    linarith
  have hPsiTr : ∀ X, (arnFamily V T X).trace = (P * X).trace := fun X => by
    rw [hrep, tr_sum_kraus]
  have hvn : (star v ⬝ᵥ (P *ᵥ v)) = (lam : ℂ) := by
    rw [hPv, dotProduct_smul, hv, smul_eq_mul, mul_one]
  set rho := vecMulVec v (star v) with hrho
  have hrho_p : rho.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have hrho_t : rho.trace = 1 := by
    rw [hrho, Matrix.trace_vecMulVec, dotProduct_comm, hv]
  have hPrho : (P * rho).trace = (lam : ℂ) := by
    rw [hrho, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm, hvn]
  -- induced norm
  have hind_bd : ∀ X : M dx, traceNorm (arnFamily V T X) ≤ lam * traceNorm X := fun X => by
    rw [hrep]; exact kraus_tn_bound K lam hq X
  have hcb_bd : ∀ (n : ℕ) (X : Matrix (Fin n × Fin dx) (Fin n × Fin dx) ℂ),
      traceNorm (amplify (arnFamily V T) n X) ≤ lam * traceNorm X := fun n X => by
    unfold amplify
    rw [amp_kraus (fun X => arnFamily V T X) K hrep X]
    exact kraus_tn_bound _ lam (quad_L K lam hq) X
  have hPsi_rho : traceNorm (arnFamily V T rho) = lam := by
    have hp : (arnFamily V T rho).PosSemidef := by rw [hrep]; exact psd_kraus_sum K hrho_p
    have := g55b_tn_psd hp
    rw [hPsiTr, hPrho] at this
    exact_mod_cast this
  have htn_rho : traceNorm rho = 1 := by
    have := g55b_tn_psd hrho_p; rw [hrho_t] at this; exact_mod_cast this
  have hind : inducedNorm 1 (arnFamily V T) = lam := by
    unfold inducedNorm
    apply le_antisymm
    · refine csSup_le ?_ ?_
      · exact ⟨_, 0, by rw [schatten_one, tn_zero]; norm_num, rfl⟩
      rintro x ⟨X, hX, rfl⟩
      rw [schatten_one] at hX ⊢
      have := hind_bd X
      nlinarith [tn_nonneg X]
    · apply le_csSup
      · refine ⟨lam, ?_⟩
        rintro x ⟨X, hX, rfl⟩
        rw [schatten_one] at hX ⊢
        have := hind_bd X
        nlinarith [tn_nonneg X]
      · exact ⟨rho, by rw [schatten_one, htn_rho], by rw [schatten_one, hPsi_rho]⟩
  -- cb witness
  set v1 : Fin 1 × Fin dx → ℂ := fun p => v p.2 with hv1
  set X1 := vecMulVec v1 (star v1) with hX1
  have hv1n : star v1 ⬝ᵥ v1 = 1 := by
    rw [← hv]; simp [hv1, dotProduct, Fintype.sum_prod_type]
  have hX1p : X1.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v1
  have htnX1 : traceNorm X1 = 1 := by
    have := g55b_tn_psd hX1p
    rw [hX1, Matrix.trace_vecMulVec, dotProduct_comm, hv1n] at this; exact_mod_cast this
  have hamp1 : traceNorm (amplify (arnFamily V T) 1 X1) = lam := by
    unfold amplify
    rw [amp_kraus (fun X => arnFamily V T X) K hrep X1]
    have hp := psd_kraus_sum (fun m => (1 : Matrix (Fin 1) (Fin 1) ℂ) ⊗ₖ K m) hX1p
    have := g55b_tn_psd hp
    rw [Matrix.trace_sum] at this
    have e : ∀ m, (((1 : Matrix (Fin 1) (Fin 1) ℂ) ⊗ₖ K m) * X1 *
        ((1 : Matrix (Fin 1) (Fin 1) ℂ) ⊗ₖ K m)ᴴ).trace =
        star (K m *ᵥ v) ⬝ᵥ (K m *ᵥ v) := by
      intro m
      rw [hX1, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec,
        Matrix.trace_vecMulVec, dotProduct_comm]
      simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, Matrix.mulVec,
        Matrix.kroneckerMap_apply, Matrix.one_apply, hv1, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        Fin.sum_univ_one]
    simp only [e] at this
    rw [quad_P, hvn] at this
    exact_mod_cast this
  have hcb : cbTraceNorm (arnFamily V T) = lam := by
    unfold cbTraceNorm cbNorm
    apply le_antisymm
    · refine csSup_le ?_ ?_
      · exact ⟨_, 0, 0, by rw [schatten_one, tn_zero]; norm_num, rfl⟩
      rintro x ⟨n, X, hX, rfl⟩
      rw [schatten_one] at hX ⊢
      have := hcb_bd n X
      nlinarith [tn_nonneg X]
    · apply le_csSup
      · refine ⟨lam, ?_⟩
        rintro x ⟨n, X, hX, rfl⟩
        rw [schatten_one] at hX ⊢
        have := hcb_bd n X
        nlinarith [tn_nonneg X]
      · exact ⟨1, X1, by rw [schatten_one, htnX1], by rw [schatten_one, hamp1]⟩
  have htrc : ∀ X, (T.transpose * complementaryMap V X).trace = (P * X).trace := fun X => by
    rw [← cl1b, hPsiTr]
  refine ⟨hind.trans hcb.symm, rho, ⟨hrho_p, hrho_t⟩, ?_, ?_⟩
  · rw [hcb, htrc, hPrho]; simp
  · intro tau htau
    rw [htrc, htrc, hPrho, Complex.ofReal_re]
    have h := G55BF.tr_psd_mul hLP htau.1
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_smul,
      htau.2, Complex.sub_re] at h
    simp at h
    linarith



lemma sum4c {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → B → C → D → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
  simp only [← Finset.sum_product']
  exact Fintype.sum_equiv (Equiv.mk (fun p => ⟨p.2.1, p.2.2.1, p.2.2.2, p.1⟩)
    (fun q => ⟨q.2.2.2, q.1, q.2.1, q.2.2.1⟩) (fun _ => rfl) (fun _ => rfl)) _ _ (fun _ => rfl)

def Pmat {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (T : M r) : M dx :=
  fun a b => ∑ y, ∑ k, ∑ l, conj (V k y a) * T l k * V l y b

lemma P_kraus {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (T B : M r)
    (hB : T = B * Bᴴ) : ∑ m, (krausOf V B m)ᴴ * krausOf V B m = Pmat V T := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, krausOf,
    Matrix.smul_apply, smul_eq_mul, star_sum, star_mul', RCLike.star_def, Pmat, hB,
    Finset.sum_mul, Finset.mul_sum]
  rw [sum4c]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

lemma Pmat_add {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (A B : M r) :
    Pmat V (A + B) = Pmat V A + Pmat V B := by
  ext a b; simp only [Pmat, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma Pmat_sub {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (A B : M r) :
    Pmat V (A - B) = Pmat V A - Pmat V B := by
  ext a b; simp only [Pmat, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma Pmat_smul {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (c : ℂ) (A : M r) :
    Pmat V (c • A) = c • Pmat V A := by
  ext a b; simp only [Pmat, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

lemma Pmat_psd {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) {T : M r}
    (hT : T.PosSemidef) : (Pmat V T).PosSemidef := by
  rw [← P_kraus V T _ (psd_sqrt_fac hT)]
  exact Matrix.posSemidef_sum _ fun m _ => Matrix.posSemidef_conjTranspose_mul_self _

lemma amp_sub {dx dy : ℕ} (Φ Ψ : Lin dx dy) (n : ℕ) (X : Matrix (Fin n × Fin dx) (Fin n × Fin dx) ℂ) :
    amplify (Φ - Ψ) n X = amplify Φ n X - amplify Ψ n X := by
  ext p q; simp [amplify, idTensorSuperop]

lemma tn_sub_le {N : Type*} [Fintype N] [DecidableEq N] (A B : Matrix N N ℂ) :
    traceNorm (A - B) ≤ traceNorm A + traceNorm B := by
  rw [sub_eq_add_neg]
  refine (tn_add_le _ _).trans (add_le_add le_rfl ?_)
  have := tn_smul_le (-1) B
  simpa using this

lemma kraus_tn_bound2 {N N' : Type*} [Fintype N] [DecidableEq N] [Fintype N'] [DecidableEq N']
    {r : ℕ} (L L' : Fin r → Matrix N' N ℂ) (lam : ℝ)
    (hQ : ∀ w : N → ℂ, ∑ m, (star (L m *ᵥ w) ⬝ᵥ (L m *ᵥ w)).re +
      ∑ m, (star (L' m *ᵥ w) ⬝ᵥ (L' m *ᵥ w)).re ≤ lam * (star w ⬝ᵥ w).re)
    (X : Matrix N N ℂ) :
    traceNorm (∑ m, L m * X * (L m)ᴴ - ∑ m, L' m * X * (L' m)ᴴ) ≤ lam * traceNorm X := by
  obtain ⟨a, b, hX, ha, hb⟩ := rank_one_dec X
  have e : ∀ L : Fin r → Matrix N' N ℂ, ∑ m, L m * X * (L m)ᴴ =
      ∑ j, ∑ m, vecMulVec (L m *ᵥ a j) (star (L m *ᵥ b j)) := by
    intro L
    rw [hX, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]
  rw [e L, e L', ← Finset.sum_sub_distrib]
  refine (tn_sum_le _ _).trans ?_
  have hr1 : ∀ (L : Fin r → Matrix N' N ℂ) (x y : N → ℂ),
      traceNorm (∑ m, vecMulVec (L m *ᵥ x) (star (L m *ᵥ y))) ≤
        ∑ m, ((star (L m *ᵥ x) ⬝ᵥ (L m *ᵥ x)).re + (star (L m *ᵥ y) ⬝ᵥ (L m *ᵥ y)).re) / 2 :=
    fun L x y => (tn_sum_le _ _).trans (Finset.sum_le_sum fun m _ => tn_rank1 _ _)
  calc ∑ j, traceNorm (∑ m, vecMulVec (L m *ᵥ a j) (star (L m *ᵥ b j)) -
        ∑ m, vecMulVec (L' m *ᵥ a j) (star (L' m *ᵥ b j)))
      ≤ ∑ j, lam * ((star (a j) ⬝ᵥ a j).re + (star (b j) ⬝ᵥ b j).re) / 2 := by
        refine Finset.sum_le_sum fun j _ => (tn_sub_le _ _).trans ?_
        have h1 := hr1 L (a j) (b j)
        have h2 := hr1 L' (a j) (b j)
        have q1 := hQ (a j)
        have q2 := hQ (b j)
        rw [← Finset.sum_div, Finset.sum_add_distrib] at h1 h2
        rw [mul_add]
        linarith
    _ = lam * traceNorm X := by
        rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib, ha, hb]; ring

lemma quad_L2 {dx dy r n : ℕ} (K K' : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (lam : ℝ)
    (hq : ∀ u : Fin dx → ℂ, ∑ m, (star (K m *ᵥ u) ⬝ᵥ (K m *ᵥ u)).re +
      ∑ m, (star (K' m *ᵥ u) ⬝ᵥ (K' m *ᵥ u)).re ≤ lam * (star u ⬝ᵥ u).re)
    (w : Fin n × Fin dx → ℂ) :
    ∑ m, (star (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ K m) *ᵥ w) ⬝ᵥ
      (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ K m) *ᵥ w)).re +
    ∑ m, (star (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ K' m) *ᵥ w) ⬝ᵥ
      (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ K' m) *ᵥ w)).re ≤ lam * (star w ⬝ᵥ w).re := by
  have hL : ∀ (K : Fin r → Matrix (Fin dy) (Fin dx) ℂ) m,
      star (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ K m) *ᵥ w) ⬝ᵥ
      (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ K m) *ᵥ w) =
      ∑ i, star (K m *ᵥ fun a => w (i, a)) ⬝ᵥ (K m *ᵥ fun a => w (i, a)) := by
    intro K m
    have hL0 : ∀ (i : Fin n) (y : Fin dy), (((1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ K m) *ᵥ w) (i, y) =
        (K m *ᵥ fun a => w (i, a)) y := by
      intro i y
      simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.one_apply,
        Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
        Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, hL0]
  have e2 : star w ⬝ᵥ w = ∑ i, star (fun a => w (i, a)) ⬝ᵥ (fun a => w (i, a)) := by
    simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply]
  simp only [hL, Complex.re_sum]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun m i => (star (K' m *ᵥ fun a => w (i, a)) ⬝ᵥ
    (K' m *ᵥ fun a => w (i, a))).re), ← Finset.sum_add_distrib, e2, Complex.re_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hq (fun a => w (i, a))

lemma quad_of_psd {dx dy r : ℕ} (K : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (Q : M dx) (lam : ℝ)
    (hK : ∑ m, (K m)ᴴ * K m = Q) (hLQ : ((lam : ℂ) • (1 : M dx) - Q).PosSemidef)
    (u : Fin dx → ℂ) :
    ∑ m, (star (K m *ᵥ u) ⬝ᵥ (K m *ᵥ u)).re ≤ lam * (star u ⬝ᵥ u).re := by
  rw [← Complex.re_sum, quad_P, hK]
  have h := (Complex.nonneg_iff.1 (hLQ.dotProduct_mulVec_nonneg u)).1
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul] at h
  linarith

lemma cb_le_of {dx dy : ℕ} (Ψ : Lin dx dy) (lam : ℝ) (hlam : 0 ≤ lam)
    (h : ∀ (n : ℕ) (X : Matrix (Fin n × Fin dx) (Fin n × Fin dx) ℂ),
      traceNorm (amplify Ψ n X) ≤ lam * traceNorm X) : cbTraceNorm Ψ ≤ lam := by
  unfold cbTraceNorm cbNorm
  refine csSup_le ?_ ?_
  · exact ⟨_, 0, 0, by rw [schatten_one, tn_zero]; norm_num, rfl⟩
  rintro x ⟨n, X, hX, rfl⟩
  rw [schatten_one] at hX ⊢
  have := h n X
  nlinarith [tn_nonneg X]

lemma cb_ge_of {dx dy : ℕ} (Ψ : Lin dx dy) (lam : ℝ)
    (h : ∀ (n : ℕ) (X : Matrix (Fin n × Fin dx) (Fin n × Fin dx) ℂ),
      traceNorm (amplify Ψ n X) ≤ lam * traceNorm X) (hlam : 0 ≤ lam)
    (n : ℕ) (X : Matrix (Fin n × Fin dx) (Fin n × Fin dx) ℂ) (hX : traceNorm X ≤ 1) :
    traceNorm (amplify Ψ n X) ≤ cbTraceNorm Ψ := by
  unfold cbTraceNorm cbNorm
  apply le_csSup
  · refine ⟨lam, ?_⟩
    rintro x ⟨n, X, hX, rfl⟩
    rw [schatten_one] at hX ⊢
    have := h n X
    nlinarith [tn_nonneg X]
  · exact ⟨n, X, by rw [schatten_one]; exact hX, by rw [schatten_one]⟩

/-- amplified witness value for a Kraus map: unit v gives sum_m ||K_m v||^2. -/
lemma amp_witness {dx dy r : ℕ} (Ψ : Lin dx dy) (K : Fin r → Matrix (Fin dy) (Fin dx) ℂ)
    (hrep : ∀ X, Ψ X = ∑ m, K m * X * (K m)ᴴ) (v : Fin dx → ℂ) (hv : star v ⬝ᵥ v = 1) :
    ∃ X1 : Matrix (Fin 1 × Fin dx) (Fin 1 × Fin dx) ℂ, traceNorm X1 = 1 ∧
      traceNorm (amplify Ψ 1 X1) = (star v ⬝ᵥ ((∑ m, (K m)ᴴ * K m) *ᵥ v)).re := by
  set v1 : Fin 1 × Fin dx → ℂ := fun p => v p.2 with hv1
  set X1 := vecMulVec v1 (star v1) with hX1
  have hv1n : star v1 ⬝ᵥ v1 = 1 := by
    rw [← hv]; simp [hv1, dotProduct, Fintype.sum_prod_type]
  have hX1p : X1.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v1
  refine ⟨X1, ?_, ?_⟩
  · have := g55b_tn_psd hX1p
    rw [hX1, Matrix.trace_vecMulVec, dotProduct_comm, hv1n] at this; exact_mod_cast this
  · unfold amplify
    rw [amp_kraus (fun X => Ψ X) K hrep X1]
    have hp := psd_kraus_sum (fun m => (1 : Matrix (Fin 1) (Fin 1) ℂ) ⊗ₖ K m) hX1p
    have := g55b_tn_psd hp
    rw [Matrix.trace_sum] at this
    have e : ∀ m, (((1 : Matrix (Fin 1) (Fin 1) ℂ) ⊗ₖ K m) * X1 *
        ((1 : Matrix (Fin 1) (Fin 1) ℂ) ⊗ₖ K m)ᴴ).trace =
        star (K m *ᵥ v) ⬝ᵥ (K m *ᵥ v) := by
      intro m
      rw [hX1, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec,
        Matrix.trace_vecMulVec, dotProduct_comm]
      simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, Matrix.mulVec,
        Matrix.kroneckerMap_apply, Matrix.one_apply, hv1, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        Fin.sum_univ_one]
    simp only [e] at this
    rw [quad_P] at this
    have h2 := congrArg Complex.re this
    rwa [Complex.ofReal_re] at h2

end S64P50


section
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P50 S64P50 S64FC S64FC2 S64T6

lemma cb_zero_dim {dy : ℕ} (Ψ : Lin 0 dy) : cbTraceNorm Ψ = 0 := by
  have h : ∀ (n : ℕ) (X : Matrix (Fin n × Fin 0) (Fin n × Fin 0) ℂ),
      traceNorm (amplify Ψ n X) ≤ 0 * traceNorm X := by
    intro n X
    have hX : X = 0 := by ext p q; exact Fin.elim0 p.2
    subst hX
    have : amplify Ψ n 0 = 0 := by
      ext p q
      simp only [amplify, idTensorSuperop, Matrix.of_apply, Matrix.zero_apply]
      have : (Matrix.of fun (i i' : Fin 0) => (0 : ℂ)) = 0 := by ext i; exact Fin.elim0 i
      rw [this, map_zero]; rfl
    rw [this, tn_zero]; simp
  apply le_antisymm (cb_le_of Ψ 0 le_rfl h)
  have := cb_ge_of Ψ 0 h le_rfl 0 0 (by rw [tn_zero]; norm_num)
  exact (tn_nonneg _).trans this

open scoped Matrix.Norms.L2Operator in
lemma spec_nonneg {N : Type*} [Fintype N] [DecidableEq N] (D : Matrix N N ℂ) : 0 ≤ specNorm D := by
  unfold specNorm; exact norm_nonneg D

end


namespace S65P48
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P50 S64P50 S64FC S64FC2 S64T6 Matrix

open scoped MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]

lemma min_eig_psd [Nonempty N] {G : Matrix N N ℂ} (hG : G.IsHermitian) :
    (G - (minEigenvalue G : ℂ) • (1 : Matrix N N ℂ)).PosSemidef := by
  have hc : 0 < Fintype.card N := Fintype.card_pos
  have hle : ∀ i, minEigenvalue G ≤ hG.eigenvalues i := by
    intro i
    unfold minEigenvalue ascEigenvalues
    rw [dif_pos hc, dif_pos hG]
    simp only [Matrix.IsHermitian.eigenvalues]
    apply hG.eigenvalues₀_antitone
    rw [Fin.le_def]
    simp only [Fin.val_rev]
    omega
  have e : G - (minEigenvalue G : ℂ) • (1 : Matrix N N ℂ) =
      cfc (fun t : ℝ => t - minEigenvalue G) G := by
    rw [cfc_sub (fun t => t) (fun _ => minEigenvalue G) G, cfc_const (minEigenvalue G) G, cfc_id' ℝ G]
    simp [Algebra.algebraMap_eq_smul_one]
  rw [e, ← Matrix.nonneg_iff_posSemidef]
  apply cfc_nonneg
  intro t ht
  rw [hG.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  linarith [hle i]

lemma quad_ge {G : Matrix N N ℂ} {c : ℝ} (h : (G - (c : ℂ) • (1 : Matrix N N ℂ)).PosSemidef)
    (y : N → ℂ) : c * (star y ⬝ᵥ y).re ≤ (star y ⬝ᵥ (G *ᵥ y)).re := by
  have h1 := (Complex.nonneg_iff.1 (h.dotProduct_mulVec_nonneg y)).1
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul] at h1
  linarith

lemma re_swap (x y : N → ℂ) : (star y ⬝ᵥ x).re = (star x ⬝ᵥ y).re := by
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]; ring

lemma amgm (x y : N → ℂ) :
    2 * (star x ⬝ᵥ y).re ≤ (star x ⬝ᵥ x).re + (star y ⬝ᵥ y).re := by
  have h := dot_star_re_nonneg (x - y)
  rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub] at h
  simp only [Complex.sub_re] at h
  have := re_swap y x
  linarith

lemma tr_le_of {C X : Matrix N N ℂ} {c : ℝ}
    (h : ∀ a b : N → ℂ, (star b ⬝ᵥ (C *ᵥ a)).re ≤ c * ((star a ⬝ᵥ a).re + (star b ⬝ᵥ b).re) / 2) :
    (C * X).trace.re ≤ c * traceNorm X := by
  obtain ⟨a, b, hX, ha, hb⟩ := rank_one_dec X
  nth_rewrite 1 [hX]
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  calc ∑ j, (C * vecMulVec (a j) (star (b j))).trace.re
      ≤ ∑ j, c * ((star (a j) ⬝ᵥ a j).re + (star (b j) ⬝ᵥ b j).re) / 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
        exact h _ _
    _ = c * traceNorm X := by
        rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib, ha, hb]; ring

lemma dot_zero_of {y : N → ℂ} (h : (star y ⬝ᵥ y).re ≤ 0) : y = 0 := by
  have h0 : star y ⬝ᵥ y = 0 := by
    rw [dot_star_real]
    have := dot_star_re_nonneg y
    have : (star y ⬝ᵥ y).re = 0 := le_antisymm h this
    rw [this]; simp
  exact dotProduct_star_self_eq_zero.1 h0

lemma lower_tn {r : ℕ} (hr : 0 < r) (W : Matrix N (Fin r) ℂ) (D : M r) :
    minEigenvalue (Wᴴ * W) * traceNorm D ≤ traceNorm (W * D * Wᴴ) := by
  set G := Wᴴ * W with hGdef
  set lam := minEigenvalue G with hlam
  rcases le_or_gt lam 0 with hl | hl
  · nlinarith [tn_nonneg D, tn_nonneg (W * D * Wᴴ)]
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hGh : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self W
  have hq : ∀ y, lam * (star y ⬝ᵥ y).re ≤ (star y ⬝ᵥ (G *ᵥ y)).re := quad_ge (min_eig_psd hGh)
  have hdet : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have := hq v
    rw [hv, dotProduct_zero, Complex.zero_re] at this
    exact hv0 (dot_zero_of (by nlinarith [dot_star_re_nonneg v]))
  set Gi := G⁻¹ with hGi
  have h1 : Gi * G = 1 := Matrix.nonsing_inv_mul G hdet
  have h2 : G * Gi = 1 := Matrix.mul_nonsing_inv G hdet
  have hGiH : Giᴴ = Gi := by
    rw [hGi, Matrix.conjTranspose_nonsing_inv, hGh.eq]
  set Mx := W * D * Wᴴ with hMx
  have hD : D = Gi * (Wᴴ * Mx * W) * Gi := by
    have : Wᴴ * Mx * W = G * D * G := by
      simp only [hMx, hGdef, Matrix.mul_assoc]
    rw [this]
    calc D = (Gi * G) * D * (G * Gi) := by rw [h1, h2]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  obtain ⟨U, hU1, hU2, htr, -, -⟩ := g55b_polar_tr D
  set C := W * Gi * Uᴴ * Gi * Wᴴ with hC
  have htrC : (Uᴴ * D).trace = (C * Mx).trace := by
    rw [hD, hC]
    rw [show W * Gi * Uᴴ * Gi * Wᴴ * Mx = W * (Gi * (Uᴴ * Gi * Wᴴ * Mx)) by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm W]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm Gi]
    simp only [Matrix.mul_assoc]
  -- key vector bound
  have hp : ∀ a : N → ℂ, lam * (star (Gi *ᵥ (Wᴴ *ᵥ a)) ⬝ᵥ (Gi *ᵥ (Wᴴ *ᵥ a))).re ≤
      (star a ⬝ᵥ a).re := by
    intro a
    set p := Gi *ᵥ (Wᴴ *ᵥ a) with hpdef
    have hGp : G *ᵥ p = Wᴴ *ᵥ a := by rw [hpdef, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    have hs1 : star p ⬝ᵥ (G *ᵥ p) = star (W *ᵥ p) ⬝ᵥ (W *ᵥ p) := by
      rw [hGdef, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    have hs2 : star p ⬝ᵥ (G *ᵥ p) = star (W *ᵥ p) ⬝ᵥ a := by
      rw [hGp, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    have hm := amgm (W *ᵥ p) a
    have := hq p
    rw [← hs1] at hm
    rw [← hs2] at hm
    linarith
  have hCb : ∀ a b : N → ℂ, (star b ⬝ᵥ (C *ᵥ a)).re ≤
      lam⁻¹ * ((star a ⬝ᵥ a).re + (star b ⬝ᵥ b).re) / 2 := by
    intro a b
    set p := Gi *ᵥ (Wᴴ *ᵥ a)
    set q := Gi *ᵥ (Wᴴ *ᵥ b) with hqdef
    have e : star b ⬝ᵥ (C *ᵥ a) = star q ⬝ᵥ (Uᴴ *ᵥ p) := by
      rw [hC]
      simp only [← Matrix.mulVec_mulVec]
      rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
      congr 1
      rw [hqdef, Matrix.star_mulVec, Matrix.star_mulVec, hGiH, Matrix.conjTranspose_conjTranspose]
    have hUp : star (Uᴴ *ᵥ p) ⬝ᵥ (Uᴴ *ᵥ p) = star p ⬝ᵥ p := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        Matrix.conjTranspose_conjTranspose, hU2, Matrix.one_mulVec]
    have hm := amgm q (Uᴴ *ᵥ p)
    rw [hUp] at hm
    have ha := hp a
    have hb := hp b
    rw [e]
    have hli : 0 < lam⁻¹ := inv_pos.2 hl
    have ha' : (star p ⬝ᵥ p).re ≤ lam⁻¹ * (star a ⬝ᵥ a).re := by
      rw [le_inv_mul_iff₀ hl]; linarith
    have hb' : (star q ⬝ᵥ q).re ≤ lam⁻¹ * (star b ⬝ᵥ b).re := by
      rw [le_inv_mul_iff₀ hl]; linarith
    nlinarith
  have hfin := tr_le_of (X := Mx) hCb
  rw [← htrC, htr, Complex.ofReal_re] at hfin
  rw [inv_mul_eq_div, le_div_iff₀ hl] at hfin
  linarith

end S65P48

namespace S65P48
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P50 S64P50 S64FC S64FC2 S64T6 Matrix
open scoped MatrixOrder

def Wp {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) : Matrix (Fin dx × Fin dy) (Fin r) ℂ :=
  Matrix.of fun p k => V k p.2 p.1

lemma hsa_eq {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) :
    hilbertSchmidtAdjoint (krausMap V) 1 = Pmat V 1 := by
  ext a b
  simp only [hilbertSchmidtAdjoint, krausMap, arn_apply, Pmat, Matrix.single_apply, Matrix.one_apply]
  simp only [apply_ite (starRingEnd ℂ), map_zero, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', map_sum, mul_comm]

lemma arn_r0 {dx dy : ℕ} (V : Fin 0 → Matrix (Fin dy) (Fin dx) ℂ) (T : M 0) : arnFamily V T = 0 := by
  apply LinearMap.ext; intro X; ext y z
  simp [arn_apply]

lemma cb_zero_map {dx dy : ℕ} : cbTraceNorm (0 : Lin dx dy) = 0 := by
  have h : ∀ (n : ℕ) (X : Matrix (Fin n × Fin dx) (Fin n × Fin dx) ℂ),
      traceNorm (amplify (0 : Lin dx dy) n X) ≤ 0 * traceNorm X := by
    intro n X
    have : amplify (0 : Lin dx dy) n X = 0 := by
      ext p q; simp [amplify, idTensorSuperop]
    rw [this, tn_zero]; simp
  apply le_antisymm (cb_le_of _ 0 le_rfl h)
  have := cb_ge_of _ 0 h le_rfl 0 0 (by rw [tn_zero]; norm_num)
  exact (tn_nonneg _).trans this

lemma top_le_spec {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N] {P : Matrix N N ℂ}
    (hH : P.IsHermitian) : ∃ lam : ℝ, ((lam : ℂ) • (1 : Matrix N N ℂ) - P).PosSemidef ∧
      lam ≤ specNorm P := by
  obtain ⟨i0, hi0⟩ := Finite.exists_max hH.eigenvalues
  refine ⟨hH.eigenvalues i0, ?_, (le_abs_self _).trans (eig_le_spec hH i0)⟩
  have e : (hH.eigenvalues i0 : ℂ) • (1 : Matrix N N ℂ) - P =
      cfc (fun t : ℝ => hH.eigenvalues i0 - t) P := by
    rw [cfc_sub (fun _ => hH.eigenvalues i0) (fun t => t) P, cfc_const (hH.eigenvalues i0) P,
      cfc_id' ℝ P]
    simp [Algebra.algebraMap_eq_smul_one]
  rw [e, ← Matrix.nonneg_iff_posSemidef]
  apply cfc_nonneg
  intro t ht
  rw [hH.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  linarith [hi0 i]

lemma amp_max {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (D : M r) :
    amplify (arnFamily V D) dx ((dx : ℂ)⁻¹ • vecMulVec (fun p : Fin dx × Fin dx =>
      if p.1 = p.2 then (1 : ℂ) else 0) (star fun p : Fin dx × Fin dx =>
      if p.1 = p.2 then (1 : ℂ) else 0)) =
      (dx : ℂ)⁻¹ • (Wp V * D * (Wp V)ᴴ) := by
  ext ⟨i, y⟩ ⟨j, z⟩
  simp only [amplify, idTensorSuperop, Matrix.of_apply, arn_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    smul_eq_mul, Wp, Matrix.of_apply]
  simp only [apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero, ite_mul, zero_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [RCLike.star_def]; ring

end S65P48

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P50 S64P50 S64FC S64FC2 S64T6 S65P48 in
open scoped MatrixOrder in
theorem solution {dx dy r : ℕ} (hdx : 0 < dx) (hdy : 0 < dy)
    (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (hV : LinearIndependent ℂ V)
    (T1 T2 : M r) (hT1 : T1.IsHermitian) (hT2 : T2.IsHermitian) :
    (0 < r → minEigenvalue ((krausColumnMatrix V)ᴴ * krausColumnMatrix V) / (dx : ℝ) *
      traceNorm (T1 - T2) ≤ cbTraceNorm (arnFamily V T1 - arnFamily V T2)) ∧
    cbTraceNorm (arnFamily V T1 - arnFamily V T2) ≤
      specNorm (hilbertSchmidtAdjoint (krausMap V) 1) * specNorm (T1 - T2) ∧
    (r = 0 → arnFamily V T1 = 0 ∧ arnFamily V T2 = 0 ∧ krausMap V = 0 ∧
      cbTraceNorm (arnFamily V T1 - arnFamily V T2) = 0) := by
  have hD : (T1 - T2).IsHermitian := hT1.sub hT2
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    have h1 := arn_r0 V T1
    have h2 := arn_r0 V T2
    have hk : krausMap V = 0 := arn_r0 V 1
    have hcb : cbTraceNorm (arnFamily V T1 - arnFamily V T2) = 0 := by
      rw [h1, h2, sub_zero, cb_zero_map]
    refine ⟨fun h => absurd h (lt_irrefl 0), ?_, fun _ => ⟨h1, h2, hk, hcb⟩⟩
    rw [hcb]; exact mul_nonneg (spec_nonneg _) (spec_nonneg _)
  set D := T1 - T2 with hDdef
  set Dp := cfc (fun t : ℝ => max t 0) D with hDpdef
  set Dm := cfc (fun t : ℝ => max (-t) 0) D with hDmdef
  have hDp : Dp.PosSemidef := g55bq3_cfc_psd D _ (fun t => le_max_right _ _)
  have hDm : Dm.PosSemidef := g55bq3_cfc_psd D _ (fun t => le_max_right _ _)
  have hDpm : Dp - Dm = D := g55bq3_parts D hD
  have habs : hermitianAbsoluteValue D = Dp + Dm := by
    unfold hermitianAbsoluteValue
    rw [hDpdef, hDmdef, ← cfc_add (a := D) (f := fun t : ℝ => max t 0) (g := fun t : ℝ => max (-t) 0)]
    apply cfc_congr
    intro t _
    rcases le_total t 0 with h | h
    · simp [abs_of_nonpos h, max_eq_right h, max_eq_left (neg_nonneg.2 h)]
    · simp [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.2 h)]
  set A := hermitianAbsoluteValue D with hAdef
  have hA : A.PosSemidef := by rw [habs]; exact hDp.add hDm
  set Kp := krausOf V (cfc Real.sqrt Dp)
  set Km := krausOf V (cfc Real.sqrt Dm)
  set Ka := krausOf V (cfc Real.sqrt A)
  have hKp : ∑ m, (Kp m)ᴴ * Kp m = Pmat V Dp := P_kraus V Dp _ (psd_sqrt_fac hDp)
  have hKm : ∑ m, (Km m)ᴴ * Km m = Pmat V Dm := P_kraus V Dm _ (psd_sqrt_fac hDm)
  have hKa : ∑ m, (Ka m)ᴴ * Ka m = Pmat V A := P_kraus V A _ (psd_sqrt_fac hA)
  have hrepp := kraus_rep V Dp _ (psd_sqrt_fac hDp)
  have hrepm := kraus_rep V Dm _ (psd_sqrt_fac hDm)
  set Q := Pmat V A with hQdef
  have hQp : Q.PosSemidef := Pmat_psd V hA
  have : Nonempty (Fin dx) := ⟨⟨0, hdx⟩⟩
  obtain ⟨v, hv, lam, hlam0, hQv, hLQ⟩ := top_eigen hQp
  have quadA : ∀ u : Fin dx → ℂ, ∑ m, (star (Ka m *ᵥ u) ⬝ᵥ (Ka m *ᵥ u)).re ≤
      lam * (star u ⬝ᵥ u).re := quad_of_psd Ka Q lam hKa hLQ
  have quad2 : ∀ u : Fin dx → ℂ, ∑ m, (star (Kp m *ᵥ u) ⬝ᵥ (Kp m *ᵥ u)).re +
      ∑ m, (star (Km m *ᵥ u) ⬝ᵥ (Km m *ᵥ u)).re ≤ lam * (star u ⬝ᵥ u).re := by
    intro u
    have e : ∑ m, (star (Kp m *ᵥ u) ⬝ᵥ (Kp m *ᵥ u)).re +
        ∑ m, (star (Km m *ᵥ u) ⬝ᵥ (Km m *ᵥ u)).re =
        ∑ m, (star (Ka m *ᵥ u) ⬝ᵥ (Ka m *ᵥ u)).re := by
      rw [← Complex.re_sum, ← Complex.re_sum, ← Complex.re_sum, quad_P, quad_P, quad_P, hKp, hKm,
        hKa, ← Complex.add_re, ← dotProduct_add, ← Matrix.add_mulVec, ← Pmat_add, ← habs]
    rw [e]; exact quadA u
  have hampD : ∀ (n : ℕ) (X : Matrix (Fin n × Fin dx) (Fin n × Fin dx) ℂ),
      traceNorm (amplify (arnFamily V T1 - arnFamily V T2) n X) ≤ lam * traceNorm X := by
    intro n X
    have e : arnFamily V T1 - arnFamily V T2 = arnFamily V Dp - arnFamily V Dm := by
      rw [← arn_sub, ← arn_sub, hDpm]
    rw [e, amp_sub]
    unfold amplify
    rw [amp_kraus (fun X => arnFamily V Dp X) Kp hrepp X,
      amp_kraus (fun X => arnFamily V Dm X) Km hrepm X]
    exact kraus_tn_bound2 _ _ lam (quad_L2 Kp Km lam quad2) X
  have hvQ : (star v ⬝ᵥ (Q *ᵥ v)).re = lam := by
    rw [hQv, dotProduct_smul, hv, smul_eq_mul, mul_one]; simp
  refine ⟨fun _ => ?_, ?_, fun h => absurd h (Nat.pos_iff_ne_zero.1 hrpos)⟩
  · -- lower bound via maximally entangled input
    have hG : (Wp V)ᴴ * Wp V = (krausColumnMatrix V)ᴴ * krausColumnMatrix V := by
      ext k l
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, krausColumnMatrix, Wp,
        Matrix.of_apply, Fintype.sum_prod_type]
      exact Finset.sum_comm
    have hlow := lower_tn hrpos (Wp V) D
    rw [hG] at hlow
    set φ : Fin dx × Fin dx → ℂ := fun p => if p.1 = p.2 then (1 : ℂ) else 0 with hφ
    set X := (dx : ℂ)⁻¹ • Matrix.vecMulVec φ (star φ) with hX
    have hc0 : (0 : ℂ) ≤ (dx : ℂ)⁻¹ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
      exact Complex.zero_le_real.2 (by positivity)
    have hXp : X.PosSemidef := (Matrix.posSemidef_vecMulVec_self_star φ).smul hc0
    have hφn : star φ ⬝ᵥ φ = (dx : ℂ) := by
      simp only [hφ, dotProduct, Fintype.sum_prod_type, Pi.star_apply, apply_ite star, star_one,
        star_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp
    have hX1 : traceNorm X = 1 := by
      have := g55b_tn_psd hXp
      rw [hX, Matrix.trace_smul, Matrix.trace_vecMulVec, dotProduct_comm, hφn, smul_eq_mul,
        inv_mul_cancel₀ (by exact_mod_cast hdx.ne')] at this
      exact_mod_cast this
    have hcb := cb_ge_of _ lam hampD hlam0 dx X hX1.le
    rw [hX, ← arn_sub, amp_max, arn_sub, ← hDdef] at hcb
    have hsm := tn_smul_le (dx : ℂ) ((dx : ℂ)⁻¹ • (Wp V * D * (Wp V)ᴴ))
    rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hdx.ne'), one_smul, Complex.norm_natCast] at hsm
    have hdxr : (0 : ℝ) < dx := by exact_mod_cast hdx
    rw [div_mul_eq_mul_div, div_le_iff₀ hdxr]
    nlinarith
  · -- upper bound
    have hcbD := cb_le_of _ lam hlam0 hampD
    have hP1 : (Pmat V (1 : M r)).IsHermitian := (Pmat_psd V Matrix.PosSemidef.one).1
    obtain ⟨mu, hmu, hmus⟩ := top_le_spec hP1
    have hs := abs_le_spec hD
    have hPs := Pmat_psd V hs
    rw [Pmat_sub, Pmat_smul] at hPs
    have h := (Complex.nonneg_iff.1 (hPs.dotProduct_mulVec_nonneg v)).1
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, Complex.sub_re,
      smul_eq_mul, Complex.re_ofReal_mul] at h
    have hA' : cfc (fun t : ℝ => |t|) D = A := rfl
    rw [hA', ← hQdef, hvQ] at h
    have h2 := (Complex.nonneg_iff.1 (hmu.dotProduct_mulVec_nonneg v)).1
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul, hv] at h2
    simp only [Complex.one_re, mul_one] at h2
    have hsn := spec_nonneg D
    rw [hsa_eq]
    nlinarith
