-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P53.fidelityErrorConverse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:03:48.79561+00:00
-- url     : https://prove2.me/submissions/13097c98-2051-4624-9097-e83d4ebc4618

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53

open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace

lemma g53d_sqrt_sq {n : Type} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
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

lemma g53d_sqrt_psd {n : Type} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) :
    (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma g53d_sqrt_mul_self {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc Real.sqrt (Xᴴ * X) * cfc Real.sqrt (Xᴴ * X) = Xᴴ * X := by
  have hnn : (0 : Matrix n n ℂ) ≤ Xᴴ * X :=
    Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self X)
  rw [← cfc_mul Real.sqrt Real.sqrt (Xᴴ * X)]
  conv_rhs => rw [← cfc_id ℝ (Xᴴ * X)]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma g53d_polar {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    ∃ W : Matrix n n ℂ, Wᴴ * W = 1 ∧ X = W * cfc Real.sqrt (Xᴴ * X) := by
  set P := cfc Real.sqrt (Xᴴ * X) with hPdef
  have hP : P.PosSemidef := g53d_sqrt_psd _
  have hPP : P * P = Xᴴ * X := g53d_sqrt_mul_self X
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

namespace G54F

variable {n : Type} [Fintype n] [DecidableEq n]

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
  have hRρH : Rρᴴ = Rρ := (g53d_sqrt_psd ρ).1.eq
  have hRσH : Rσᴴ = Rσ := (g53d_sqrt_psd σ).1.eq
  have hRρ2 : Rρ * Rρ = ρ := sqrt_mul_sqrt hρ
  have hRσ2 : Rσ * Rσ = σ := sqrt_mul_sqrt hσ
  obtain ⟨W, hW, hpol⟩ := g53d_polar (Rσ * Rρ)
  have hKK : (Rσ * Rρ)ᴴ * (Rσ * Rρ) = Rρ * σ * Rρ := by
    rw [Matrix.conjTranspose_mul, hRρH, hRσH, Matrix.mul_assoc, ← Matrix.mul_assoc Rσ, hRσ2,
      Matrix.mul_assoc]
  rw [hKK] at hpol
  set Ab := cfc Real.sqrt (Rρ * σ * Rρ) with hAb
  have hAbH : Abᴴ = Ab := (g53d_sqrt_psd _).1.eq
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

end G54F

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open Finset QAlgorithms QAlgorithms.Papers.Independent.Information100.P53

theorem g54_success_bound {M N : ℕ} (hM : 0 < M)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i))
    (D : Fin M → Matrix (Fin N) (Fin N) ℂ) (hD : IsPOVM D) :
    success p rho D ≤ 1 / (M : ℝ) + fidelitySum p rho / (M : ℝ) := by
  set s : Fin M → Fin M → ℝ := fun k l => (D k * ((p l : ℂ) • rho l)).trace.re with hs
  have hsucc : success p rho D = ∑ i, s i i := by
    unfold success effectProb
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hs, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hcol : ∀ l, ∑ k, s k l = p l := by
    intro l
    simp only [hs]
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hD.2, Matrix.one_mul,
      Matrix.trace_smul, (hrho l).2]
    simp
  have hpair : ∀ i j, s i i + s j j - s i j - s j i ≤
      Real.sqrt (p i ^ 2 + 2 * (1 - 2 * fidelity (rho i) (rho j)) * p i * p j + p j ^ 2) := by
    intro i j
    obtain ⟨hZ, hZ2⟩ := G54F.povm_contr D hD.1 hD.2 i j
    have := G54F.fvdg (hrho i).1 (hrho j).1 (hrho i).2 (hrho j).2 (hp.1 i) (hp.1 j) hZ hZ2
    have e : (D i - D j) * ((p i : ℂ) • rho i - (p j : ℂ) • rho j) =
        D i * ((p i : ℂ) • rho i) - D i * ((p j : ℂ) • rho j) - D j * ((p i : ℂ) • rho i) +
          D j * ((p j : ℂ) • rho j) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [e, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, Complex.add_re, Complex.sub_re,
      Complex.sub_re] at this
    unfold fidelity rootFidelity
    simp only [hs]
    linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin M))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ.filter (fun j => i < j)) => hpair i j))
  have hL : ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (s i i + s j j - s i j - s j i) =
      (∑ i : Fin M, ∑ _j : Fin M, s i i - ∑ i, s i i) - (∑ i : Fin M, ∑ j : Fin M, s i j - ∑ i, s i i) := by
    rw [← G54F.pair_sum (fun i _ => s i i), ← G54F.pair_sum s, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hL] at hsum
  have hfs : fidelitySum p rho = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      Real.sqrt (p i ^ 2 + 2 * (1 - 2 * fidelity (rho i) (rho j)) * p i * p j + p j ^ 2) := rfl
  rw [← hfs] at hsum
  have htot : ∑ i, ∑ j, s i j = 1 := by
    rw [Finset.sum_comm, ← hp.2]
    exact Finset.sum_congr rfl fun l _ => hcol l
  have hconst : ∑ i : Fin M, ∑ _j : Fin M, s i i = (M : ℝ) * ∑ i, s i i := by
    simp [Finset.sum_const, Finset.card_univ, Finset.mul_sum]
  rw [htot, hconst] at hsum
  rw [hsucc]
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [← add_div, le_div_iff₀ hM']
  nlinarith

theorem solution {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (p : Fin M → ℝ) (hp : IsPrior p)
    (rho : Fin M → Matrix (Fin N) (Fin N) ℂ) (hrho : ∀ i, IsDensityMatrix (rho i)) :
    (∀ D : Fin M → Matrix (Fin N) (Fin N) ℂ, IsPOVM D →
      1 - 1 / (M : ℝ) - fidelitySum p rho / (M : ℝ) ≤ 1 - success p rho D) ∧
    1 - 1 / (M : ℝ) - fidelitySum p rho / (M : ℝ) ≤ 1 - mixedOptSuccess p rho := by
  refine ⟨fun D hD => ?_, ?_⟩
  · have := g54_success_bound hM p hp rho hrho D hD
    linarith
  · have hfs : 0 ≤ fidelitySum p rho := by
      unfold fidelitySum pairSum
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    have : mixedOptSuccess p rho ≤ 1 / (M : ℝ) + fidelitySum p rho / (M : ℝ) := by
      unfold mixedOptSuccess
      apply Real.iSup_le
      · intro D
        exact g54_success_bound hM p hp rho hrho D.1 D.2
      · positivity
    linarith

end
