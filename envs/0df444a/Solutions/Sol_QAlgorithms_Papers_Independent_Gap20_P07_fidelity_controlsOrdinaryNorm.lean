-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P07.fidelity_controlsOrdinaryNorm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:48:53.278014+00:00
-- url     : https://prove2.me/submissions/3a0d226c-fffd-42ad-9b78-003c1d7008c1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P07

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

open S64FC S64FC2 in
theorem solution (d : ℕ) (hd : 0 < d)
    (T : Superop (Fin d) (Fin d)) (hT : IsChannel T) :
    QAlgorithms.Papers.Independent.Gap20.P07.ordinaryNorm d (fun X => T X - X) ≤ 4 * sSup {r : ℝ |
      ∃ psi : EuclideanSpace ℂ (Fin d), IsState psi ∧
        r = Real.sqrt (1 - effectProb (pureDensity psi) (T (pureDensity psi)))} := by
  obtain ⟨m, E, hE, hTE⟩ := hT
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set S := {r : ℝ | ∃ psi : EuclideanSpace ℂ (Fin d), IsState psi ∧
        r = Real.sqrt (1 - effectProb (pureDensity psi) (T (pureDensity psi)))} with hSdef
  have hpd : ∀ psi : EuclideanSpace ℂ (Fin d),
      pureDensity psi = Matrix.vecMulVec (⇑psi) (star ⇑psi) := by
    intro psi; ext a b; simp [pureDensity, Matrix.vecMulVec_apply]
  have hbdd : BddAbove S := by
    refine ⟨1, ?_⟩
    rintro r ⟨psi, -, rfl⟩
    rw [hTE, hpd, effectProb, kraus_f]
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
      Complex.normSq_nonneg (star (⇑psi) ⬝ᵥ (E j *ᵥ ⇑psi)))
    exact (Real.sqrt_le_sqrt (by linarith)).trans_eq Real.sqrt_one
  have hS : ∀ ψ : Fin d → ℂ, star ψ ⬝ᵥ ψ = 1 →
      Real.sqrt (1 - (Matrix.vecMulVec ψ (star ψ) *
        krausApply E (Matrix.vecMulVec ψ (star ψ))).trace.re) ≤ sSup S := by
    intro ψ hψ
    apply le_csSup hbdd
    refine ⟨WithLp.toLp 2 ψ, ?_, ?_⟩
    · unfold IsState
      have h2 : ‖WithLp.toLp 2 ψ‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq]
        have := congrArg Complex.re hψ
        simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.one_re] at this
        rw [← this]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
      have h0 := norm_nonneg (WithLp.toLp 2 ψ)
      nlinarith
    · rw [hTE, hpd]; rfl
  have hs0 : 0 ≤ sSup S := by
    obtain ⟨i⟩ := (inferInstance : Nonempty (Fin d))
    have hψ : star (Pi.single i (1 : ℂ)) ⬝ᵥ (Pi.single i (1 : ℂ)) = 1 := by
      simp [dotProduct, Pi.single_apply]
    exact (Real.sqrt_nonneg _).trans (hS _ hψ)
  unfold QAlgorithms.Papers.Independent.Gap20.P07.ordinaryNorm
  refine csSup_le ?_ ?_
  · exact ⟨_, 0, by rw [tn_zero]; norm_num, rfl⟩
  rintro r ⟨X, hX, rfl⟩
  have hL : T X - X = Lmap E X := by rw [Lmap_apply, hTE]
  show traceNorm (T X - X) ≤ _
  rw [hL]
  have hb := bound_X E hE (sSup S) hS X
  have := tn_nonneg X
  nlinarith

end
