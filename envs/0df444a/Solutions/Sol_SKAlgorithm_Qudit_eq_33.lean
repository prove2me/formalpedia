-- Prove2me | solution 1 for SKAlgorithm.Qudit.eq_33
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:49:20.624348+00:00
-- url     : https://prove2.me/submissions/c4169b8e-eb59-48b9-b23d-212a5ffde954

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
open QAlgorithms



open Matrix Complex
open scoped Matrix.Norms.L2Operator

namespace SKAlgorithm.Qudit.ZeroDiagonalProof

/- The following two definitions and Fourier unitarity proof are reused from
GeomDL.Grids.fourierMatrix_unitary, public theorem f8bf7035-d402-4f01-bca4-028dc3f0b91d,
actual accepted submission 8200430b-91d7-4b1d-b8b1-92ae3e619905.
The Fourier definitions retain their exact bodies from canonical model
GeomDL_Grids_Defs (d3ba1c65-bab7-45e1-b3c2-3a319ccadbfa). -/
noncomputable def fourierVec (n : ℕ) [NeZero n] (k : ZMod n) : ZMod n → ℂ :=
  fun u => ((Real.sqrt n : ℝ) : ℂ)⁻¹ *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k.val * u.val : ℕ) : ℂ) / (n : ℂ))

/-- The `n × n` Fourier matrix `Φ = (φ_0, …, φ_{n-1})`, Bronstein et al. §4.2, p. 38: its
`k`-th column is `φ_k`, so `Φ u k = φ_k(u)`. -/
noncomputable def fourierMatrix (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  fun u k => fourierVec n k u


theorem eq_of_exp_aux {n : ℕ} (hn : 0 < n) {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (n : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) / (n : ℂ))) : a = b := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp at hm
  have k2 : ((a : ℤ) : ℂ) = ((b + m * n : ℤ) : ℂ) := by
    push_cast
    linear_combination hm
  have k3 : (a : ℤ) = b + m * n := by exact_mod_cast k2
  have : m = 0 := by
    rcases lt_trichotomy m 0 with h1 | h1 | h1
    · have : m * (n:ℤ) ≤ -n := by nlinarith
      omega
    · exact h1
    · have : (n:ℤ) ≤ m * n := by nlinarith
      omega
  subst this
  omega


theorem fourierMatrix_unitary {n : ℕ} [NeZero n] :
    (fourierMatrix n)ᴴ * fourierMatrix n = 1 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  ext k l
  set ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((l.val : ℂ) - k.val) / (n : ℂ)) with hζ
  have hc : ((Real.sqrt n : ℝ) : ℂ)⁻¹ * ((Real.sqrt n : ℝ) : ℂ)⁻¹ = (n : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    push_cast; rfl
  have term : ∀ u : ZMod n, star (fourierVec n k u) * fourierVec n l u = (n : ℂ)⁻¹ * ζ ^ u.val := by
    intro u
    simp only [fourierVec, hζ, star_mul', ← Complex.exp_conj, star_inv₀, Complex.star_def,
      Complex.conj_ofReal, map_mul, map_div₀, Complex.conj_I, Complex.conj_natCast, map_ofNat]
    rw [← Complex.exp_nat_mul]
    calc _ = (((Real.sqrt n : ℝ) : ℂ)⁻¹ * ((Real.sqrt n : ℝ) : ℂ)⁻¹) *
          (Complex.exp (2 * (Real.pi : ℂ) * -Complex.I * ((k.val * u.val : ℕ) : ℂ) / (n : ℂ)) *
           Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((l.val * u.val : ℕ) : ℂ) / (n : ℂ))) := by ring
      _ = _ := by
        rw [hc, ← Complex.exp_add]
        congr 2
        push_cast; ring
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, fourierMatrix]
  rw [Finset.sum_congr rfl (fun u _ => term u), ← Finset.mul_sum]
  have hsum : ∑ u : ZMod n, ζ ^ u.val = ∑ j ∈ Finset.range n, ζ ^ j := by
    refine Finset.sum_nbij' (fun u => u.val) (fun j => (j : ZMod n)) ?_ ?_ ?_ ?_ ?_
    · intro u _; simpa using ZMod.val_lt u
    · intro j _; simp
    · intro u _; simp
    · intro j hj
      exact ZMod.val_cast_of_lt (by simpa using hj)
    · intro u _; rfl
  rw [hsum]
  by_cases hkl : k = l
  · subst hkl
    have : ζ = 1 := by rw [hζ, sub_self, mul_zero, zero_div, Complex.exp_zero]
    simp [this, hn']
  · rw [Matrix.one_apply_ne hkl]
    have hζ1 : ζ ≠ 1 := by
      intro h1
      apply hkl
      apply ZMod.val_injective n
      symm
      refine eq_of_exp_aux hn (ZMod.val_lt l) (ZMod.val_lt k) ?_
      have : 2 * (Real.pi : ℂ) * Complex.I * (l.val : ℂ) / (n : ℂ) =
          2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ) +
            2 * (Real.pi : ℂ) * Complex.I * ((l.val : ℂ) - k.val) / (n : ℂ) := by ring
      rw [this, Complex.exp_add, ← hζ, h1, mul_one]
    have hζn : ζ ^ n = 1 := by
      rw [hζ, ← Complex.exp_nat_mul]
      have : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * ((l.val : ℂ) - k.val) / (n : ℂ)) =
          (((l.val : ℤ) - k.val : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast; field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hζ1, hζn, sub_self, zero_div, mul_zero]


lemma fourierVec_flat {n : ℕ} [NeZero n] (k u : ZMod n) :
    star (fourierVec n k u) * fourierVec n k u = (n : ℂ)⁻¹ := by
  have hc : ((Real.sqrt n : ℝ) : ℂ)⁻¹ * ((Real.sqrt n : ℝ) : ℂ)⁻¹ = (n : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    push_cast
    rfl
  let z : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ((k.val * u.val : ℕ) : ℂ) / (n : ℂ)
  have hz : star z = -z := by
    simp only [z, map_div₀, map_mul, map_ofNat, Complex.star_def,
      Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast]
    ring
  change star (((Real.sqrt n : ℝ) : ℂ)⁻¹ * Complex.exp z) *
    (((Real.sqrt n : ℝ) : ℂ)⁻¹ * Complex.exp z) = _
  rw [star_mul', star_inv₀]
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj]
  change _ * Complex.exp (star z) * (_ * Complex.exp z) = _
  rw [hz]
  calc
    _ = (((Real.sqrt n : ℝ) : ℂ)⁻¹ * ((Real.sqrt n : ℝ) : ℂ)⁻¹) *
      (Complex.exp (-z) * Complex.exp z) := by ring
    _ = _ := by rw [hc, ← Complex.exp_add]; simp

noncomputable def fourierFin (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℂ :=
  (fourierMatrix n).submatrix (ZMod.finEquiv n) (ZMod.finEquiv n)

lemma fourierFin_unitary {n : ℕ} [NeZero n] :
    fourierFin n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (fourierFin n)ᴴ * fourierFin n = 1
  rw [fourierFin, Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul _ _ _ _ _ (ZMod.finEquiv n).bijective,
    fourierMatrix_unitary, Matrix.submatrix_one _ (ZMod.finEquiv n).injective]

lemma fourierFin_flat {n : ℕ} [NeZero n] (i j : Fin n) :
    star (fourierFin n i j) * fourierFin n i j = (n : ℂ)⁻¹ :=
  fourierVec_flat _ _

lemma fourierFin_diag {n : ℕ} [NeZero n] (v : Fin n → ℂ) (i : Fin n) :
    ((fourierFin n)ᴴ * Matrix.diagonal v * fourierFin n) i i =
      (n : ℂ)⁻¹ * ∑ j, v j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  calc
    _ = ∑ j, (star (fourierFin n j i) * fourierFin n j i) * v j := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp only [fourierFin_flat, Finset.mul_sum]

/-- A traceless Hermitian matrix is unitarily conjugate to a matrix with zero diagonal. -/
theorem exists_unitary_zero_diag {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ)
    (hH : H.IsHermitian) (htr : H.trace = 0) :
    ∃ U : Matrix (Fin d) (Fin d) ℂ,
      U ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ ∀ i, (Uᴴ * H * U) i i = 0 := by
  classical
  by_cases hd : d = 0
  · subst d
    exact ⟨1, (Matrix.unitaryGroup (Fin 0) ℂ).one_mem, fun i => Fin.elim0 i⟩
  by_cases hd1 : d = 1
  · subst d
    refine ⟨1, (Matrix.unitaryGroup (Fin 1) ℂ).one_mem, ?_⟩
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa [Matrix.trace, Matrix.diag] using htr
  have : NeZero d := ⟨hd⟩
  let V := hH.eigenvectorUnitary
  let W := fourierFin d
  refine ⟨(V : Matrix (Fin d) (Fin d) ℂ) * W,
    (Matrix.unitaryGroup (Fin d) ℂ).mul_mem V.property fourierFin_unitary, ?_⟩
  intro i
  have he : (V : Matrix (Fin d) (Fin d) ℂ)ᴴ * H * V =
      Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ)) := by
    simpa only [V, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      hH.conjStarAlgAut_star_eigenvectorUnitary
  have ht : ∑ j, (hH.eigenvalues j : ℂ) = 0 :=
    hH.trace_eq_sum_eigenvalues.symm.trans htr
  have hreassoc : ((V : Matrix (Fin d) (Fin d) ℂ) * W)ᴴ * H * (V * W) =
      Wᴴ * ((V : Matrix (Fin d) (Fin d) ℂ)ᴴ * H * V) * W := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [hreassoc, he]
  change ((fourierFin d)ᴴ * Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ)) * fourierFin d) i i = 0
  rw [fourierFin_diag, ht, mul_zero]

end SKAlgorithm.Qudit.ZeroDiagonalProof


noncomputable section
namespace SKAlgorithm.Qudit.LieProof

variable {d : ℕ}

def diagonalGenerator (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i => ((i.val : ℝ) - ((d : ℝ) - 1) / 2 : ℝ))

def offDiagonalGenerator (H : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => Complex.I * H i j / ((j.val : ℂ) - (i.val : ℂ))

lemma diagonalGenerator_hermitian (d : ℕ) : (diagonalGenerator d).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  change star ((((i.val : ℝ) - ((d : ℝ) - 1) / 2) : ℝ) : ℂ) = _
  exact Complex.conj_ofReal _

lemma offDiagonalGenerator_hermitian (H : Matrix (Fin d) (Fin d) ℂ)
    (hH : H.IsHermitian) : (offDiagonalGenerator H).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star (Complex.I * H j i / ((i.val : ℂ) - j.val)) =
    Complex.I * H i j / ((j.val : ℂ) - i.val)
  simp only [map_div₀, map_mul, map_sub, Complex.star_def, Complex.conj_I,
    Complex.conj_natCast]
  have hh := hH.apply i j
  change (starRingEnd ℂ) (H j i) = H i j at hh
  rw [hh]
  rw [show (i.val : ℂ) - j.val = -((j.val : ℂ) - i.val) by ring]
  simp only [neg_mul, neg_div_neg_eq]

lemma offDiagonalGenerator_commutator (H : Matrix (Fin d) (Fin d) ℂ)
    (hdiag : ∀ i, H i i = 0) :
    offDiagonalGenerator H * diagonalGenerator d -
      diagonalGenerator d * offDiagonalGenerator H = Complex.I • H := by
  ext i j
  simp only [offDiagonalGenerator, diagonalGenerator, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.sub_apply, Matrix.of_apply, Matrix.smul_apply,
    smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp [hdiag]
  · have hij' : (j.val : ℂ) - i.val ≠ 0 := by
      intro h
      have hval : j.val = i.val := by exact_mod_cast sub_eq_zero.mp h
      exact hij (Fin.ext hval.symm)
    push_cast
    field_simp
    ring

lemma diagonalGenerator_norm (hd : 1 ≤ d) :
    specNorm (diagonalGenerator d) ≤ ((d : ℝ) - 1) / 2 := by
  change ‖diagonalGenerator d‖ ≤ _
  rw [diagonalGenerator, Matrix.l2_opNorm_diagonal]
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ ((d : ℝ) - 1) / 2)).mpr
  intro i
  rw [Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  have hi : (i.val : ℝ) ≤ (d : ℝ) - 1 := by exact_mod_cast Nat.le_sub_one_of_lt i.isLt
  have hz : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  constructor <;> linarith

lemma offDiagonalGenerator_entry_norm (H : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    ‖offDiagonalGenerator H i j‖ ≤ ‖H i j‖ := by
  by_cases hij : i = j
  · subst j
    simp [offDiagonalGenerator]
  · have hdif : (1 : ℝ) ≤ |(j.val : ℝ) - i.val| := by
      have hne : j.val ≠ i.val := fun h => hij (Fin.ext h.symm)
      rcases lt_or_gt_of_ne hne with h | h
      · have hc : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast h
        have ha := neg_le_abs ((j.val : ℝ) - i.val)
        linarith
      · have hc : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
        have ha := le_abs_self ((j.val : ℝ) - i.val)
        linarith
    have hnorm : (1 : ℝ) ≤ ‖(j.val : ℂ) - i.val‖ := by
      simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] using hdif
    simp only [offDiagonalGenerator, Matrix.of_apply, norm_div, norm_mul, Complex.norm_I,
      one_mul]
    exact div_le_self (norm_nonneg _) hnorm

end SKAlgorithm.Qudit.LieProof

noncomputable section
namespace SKAlgorithm.Qudit.LieNormProof

variable {d : ℕ}

lemma specNorm_nonneg (A : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ specNorm A := norm_nonneg A

lemma row_norm_bound (A : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d))
    (i : Fin d) :
    ‖(A *ᵥ x) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ ^ 2) * ‖x‖ ^ 2 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 (fun j => star (A i j)) :
    EuclideanSpace ℂ (Fin d)) x
  have heq : inner ℂ (WithLp.toLp 2 (fun j => star (A i j)) :
      EuclideanSpace ℂ (Fin d)) x = (A *ᵥ x) i := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec, mul_comm]
  rw [heq] at h
  have hsq := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  simpa [EuclideanSpace.norm_sq_eq, norm_star, mul_pow] using hsq

lemma specNorm_le_sqrt_mass (A : Matrix (Fin d) (Fin d) ℂ) :
    specNorm A ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  change ‖A‖ ≤ _
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ i, ‖(A *ᵥ x) i‖ ^ 2) ≤ _
  calc
    _ ≤ ∑ i, (∑ j, ‖A i j‖ ^ 2) * ‖x‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => row_norm_bound A x i)
    _ = _ := (Finset.sum_mul _ _ _).symm

lemma specNorm_sq_le_mass (A : Matrix (Fin d) (Fin d) ℂ) :
    specNorm A ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have h := sq_le_sq₀ (specNorm_nonneg A) (Real.sqrt_nonneg (∑ i, ∑ j, ‖A i j‖ ^ 2))
  have hsq := h.mpr (specNorm_le_sqrt_mass A)
  simpa only [Real.sq_sqrt (by positivity : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2)] using hsq

lemma mass_le_card_norm_sq (A : Matrix (Fin d) (Fin d) ℂ) :
    (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤ (d : ℝ) * specNorm A ^ 2 := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j : Fin d, specNorm A ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := Matrix.l2_opNorm_mulVec A
        (WithLp.toLp 2 (Pi.single j (1 : ℂ)) : EuclideanSpace ℂ (Fin d))
      have hu : ‖(WithLp.toLp 2 (Pi.single j (1 : ℂ)) : EuclideanSpace ℂ (Fin d))‖ = 1 := by
        simp
      rw [hu, mul_one] at h
      have hsq := (sq_le_sq₀ (norm_nonneg _) (specNorm_nonneg A)).mpr h
      simpa [EuclideanSpace.norm_sq_eq, Matrix.mulVec_single] using hsq
    _ = _ := by simp

lemma norm_bound_of_entries (A H : Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ i j, ‖A i j‖ ≤ ‖H i j‖) :
    specNorm A ≤ Real.sqrt d * specNorm H := by
  have hm : (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤ ∑ i, ∑ j, ‖H i j‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h i j)
  have hs := (specNorm_sq_le_mass A).trans (hm.trans (mass_le_card_norm_sq H))
  apply (sq_le_sq₀ (specNorm_nonneg A)
    (mul_nonneg (Real.sqrt_nonneg _) (specNorm_nonneg H))).mp
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)] using hs

end SKAlgorithm.Qudit.LieNormProof

noncomputable section
namespace SKAlgorithm.Qudit.LieBalanceProof

variable {d : ℕ}

lemma balanced_rescaling (F G H : Matrix (Fin d) (Fin d) ℂ)
    (hF : F.IsHermitian) (hG : G.IsHermitian)
    (hcomm : F * G - G * F = Complex.I • H)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hFa : specNorm F ≤ a) (hGb : specNorm G ≤ b) :
    ∃ F' G' : Matrix (Fin d) (Fin d) ℂ,
      F'.IsHermitian ∧ G'.IsHermitian ∧ F' * G' - G' * F' = Complex.I • H ∧
      specNorm F' ≤ Real.sqrt a * Real.sqrt b ∧
      specNorm G' ≤ Real.sqrt a * Real.sqrt b := by
  let r := Real.sqrt b / Real.sqrt a
  let s := Real.sqrt a / Real.sqrt b
  have hra : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hrb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hr : 0 ≤ r := le_of_lt (div_pos hrb hra)
  have hs : 0 ≤ s := le_of_lt (div_pos hra hrb)
  have hrs : r * s = 1 := by dsimp [r, s]; field_simp
  have hra' : r * a = Real.sqrt a * Real.sqrt b := by
    dsimp [r]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (ne_of_gt hra)).mpr
    calc
      _ = Real.sqrt b * (Real.sqrt a * Real.sqrt a) := by rw [Real.mul_self_sqrt ha.le]
      _ = _ := by ring
  have hsb' : s * b = Real.sqrt a * Real.sqrt b := by
    dsimp [s]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (ne_of_gt hrb)).mpr
    calc
      _ = Real.sqrt a * (Real.sqrt b * Real.sqrt b) := by rw [Real.mul_self_sqrt hb.le]
      _ = _ := by ring
  refine ⟨r • F, s • G, ?_, ?_, ?_, ?_, ?_⟩
  · exact hF.smul (IsSelfAdjoint.all r)
  · exact hG.smul (IsSelfAdjoint.all s)
  · calc
      (r • F) * (s • G) - (s • G) * (r • F) = (r * s) • (F * G - G * F) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub]
        rw [mul_comm s r]
      _ = Complex.I • H := by rw [hrs, one_smul, hcomm]
  · change ‖r • F‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left hFa hr).trans_eq hra'
  · change ‖s • G‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
    exact (mul_le_mul_of_nonneg_left hGb hs).trans_eq hsb'

lemma balance_constant (d : ℕ) (c : ℝ) :
    Real.sqrt (Real.sqrt d * c) * Real.sqrt (((d : ℝ) - 1) / 2) =
      (d : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (((d : ℝ) - 1) / 2) * Real.sqrt c := by
  rw [Real.sqrt_mul (Real.sqrt_nonneg _)]
  have hquarter : Real.sqrt (Real.sqrt (d : ℝ)) = (d : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg d)]
    norm_num
  rw [hquarter]
  ring

end SKAlgorithm.Qudit.LieBalanceProof

noncomputable section
namespace SKAlgorithm.Qudit.LieTransportProof

variable {d : ℕ}

lemma specNorm_unitary_conjugate (U A : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    specNorm (U * A * Uᴴ) = specNorm A := by
  change ‖U * A * Uᴴ‖ = ‖A‖
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ := Unitary.star_mem hU
  exact (CStarRing.norm_mul_mem_unitary (U * A) hUstar).trans
    (CStarRing.norm_mem_unitary_mul A hU)

lemma commutator_transport (U F G H : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hcomm : F * G - G * F = Complex.I • (Uᴴ * H * U)) :
    (U * F * Uᴴ) * (U * G * Uᴴ) - (U * G * Uᴴ) * (U * F * Uᴴ) =
      Complex.I • H := by
  have hleft : Uᴴ * U = 1 := hU.1
  have hright : U * Uᴴ = 1 := hU.2
  calc
    _ = U * (F * G - G * F) * Uᴴ := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hleft, Matrix.one_mul]
    _ = U * (Complex.I • (Uᴴ * H * U)) * Uᴴ := by rw [hcomm]
    _ = Complex.I • H := by
      simp only [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      calc
        U * (Uᴴ * H * U) * Uᴴ = (U * Uᴴ) * H * (U * Uᴴ) := by
          simp only [Matrix.mul_assoc]
        _ = H := by rw [hright, Matrix.one_mul, Matrix.mul_one]

end SKAlgorithm.Qudit.LieTransportProof


namespace SKAlgorithm.Qudit.LieProof

lemma sum_fin_val (d : ℕ) :
    (∑ i : Fin d, (i.val : ℝ)) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
      ring

lemma diagonalGenerator_trace (d : ℕ) : (diagonalGenerator d).trace = 0 := by
  simp only [diagonalGenerator, Matrix.trace_diagonal]
  have hreal : (∑ i : Fin d, ((i.val : ℝ) - ((d : ℝ) - 1) / 2)) = 0 := by
    rw [Finset.sum_sub_distrib, sum_fin_val]
    simp
    ring
  exact_mod_cast hreal

lemma offDiagonalGenerator_trace {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) :
    (offDiagonalGenerator H).trace = 0 := by
  simp [offDiagonalGenerator, Matrix.trace, Matrix.diag]

end SKAlgorithm.Qudit.LieProof

namespace SKAlgorithm.Qudit.LieBalanceProof
variable {d : ℕ}
lemma balanced_rescaling_traceless (F G H : Matrix (Fin d) (Fin d) ℂ)
    (hF : F.IsHermitian) (hG : G.IsHermitian)
    (htrF : F.trace = 0) (htrG : G.trace = 0)
    (hcomm : F * G - G * F = Complex.I • H)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hFa : specNorm F ≤ a) (hGb : specNorm G ≤ b) :
    ∃ F' G' : Matrix (Fin d) (Fin d) ℂ,
      F'.IsHermitian ∧ G'.IsHermitian ∧ F'.trace = 0 ∧ G'.trace = 0 ∧ F' * G' - G' * F' = Complex.I • H ∧
      specNorm F' ≤ Real.sqrt a * Real.sqrt b ∧
      specNorm G' ≤ Real.sqrt a * Real.sqrt b := by
  let r := Real.sqrt b / Real.sqrt a
  let s := Real.sqrt a / Real.sqrt b
  have hra : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hrb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hr : 0 ≤ r := le_of_lt (div_pos hrb hra)
  have hs : 0 ≤ s := le_of_lt (div_pos hra hrb)
  have hrs : r * s = 1 := by dsimp [r, s]; field_simp
  have hra' : r * a = Real.sqrt a * Real.sqrt b := by
    dsimp [r]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (ne_of_gt hra)).mpr
    calc
      _ = Real.sqrt b * (Real.sqrt a * Real.sqrt a) := by rw [Real.mul_self_sqrt ha.le]
      _ = _ := by ring
  have hsb' : s * b = Real.sqrt a * Real.sqrt b := by
    dsimp [s]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (ne_of_gt hrb)).mpr
    calc
      _ = Real.sqrt a * (Real.sqrt b * Real.sqrt b) := by rw [Real.mul_self_sqrt hb.le]
      _ = _ := by ring
  refine ⟨r • F, s • G, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hF.smul (IsSelfAdjoint.all r)
  · exact hG.smul (IsSelfAdjoint.all s)
  · simp [Matrix.trace_smul, htrF]
  · simp [Matrix.trace_smul, htrG]
  · calc
      (r • F) * (s • G) - (s • G) * (r • F) = (r * s) • (F * G - G * F) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub]
        rw [mul_comm s r]
      _ = Complex.I • H := by rw [hrs, one_smul, hcomm]
  · change ‖r • F‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left hFa hr).trans_eq hra'
  · change ‖s • G‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
    exact (mul_le_mul_of_nonneg_left hGb hs).trans_eq hsb'


end SKAlgorithm.Qudit.LieBalanceProof

namespace SKAlgorithm.Qudit
theorem balanced_traceless {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (htr : H.trace = 0) :
    ∃ F G : Matrix (Fin d) (Fin d) ℂ, F.IsHermitian ∧ G.IsHermitian ∧ F.trace = 0 ∧ G.trace = 0 ∧
      F * G - G * F = Complex.I • H ∧
      specNorm F ≤ (d : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (((d : ℝ) - 1) / 2) * Real.sqrt (specNorm H) ∧
      specNorm G ≤ (d : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (((d : ℝ) - 1) / 2) * Real.sqrt (specNorm H) := by
  classical
  by_cases hzero : H = 0
  · subst H
    refine ⟨0, 0, Matrix.isHermitian_zero, Matrix.isHermitian_zero, by simp, by simp, by simp, ?_, ?_⟩ <;>
      simp [specNorm]
  have hd : 2 ≤ d := by
    by_contra h
    have hcases : d = 0 ∨ d = 1 := by omega
    apply hzero
    rcases hcases with rfl | rfl
    · ext i j
      exact Fin.elim0 i
    · have he : H 0 0 = 0 := by simpa [Matrix.trace, Matrix.diag] using htr
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      simpa [hi, hj] using he
  obtain ⟨U, hU, hdiag⟩ := ZeroDiagonalProof.exists_unitary_zero_diag H hH htr
  let K := Uᴴ * H * U
  have hK : K.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul U hH
  have hnormK : specNorm K = specNorm H := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      LieTransportProof.specNorm_unitary_conjugate Uᴴ H (Unitary.star_mem hU)
  have hpos : 0 < specNorm K := by
    rw [hnormK]
    exact norm_pos_iff.mpr hzero
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hb : (0 : ℝ) < ((d : ℝ) - 1) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨F, G, hF, hG, htrF, htrG, hFG, hFn, hGn⟩ :=
    LieBalanceProof.balanced_rescaling_traceless (LieProof.offDiagonalGenerator K)
      (LieProof.diagonalGenerator d) K
      (LieProof.offDiagonalGenerator_hermitian K hK)
      (LieProof.diagonalGenerator_hermitian d)
      (LieProof.offDiagonalGenerator_trace K) (LieProof.diagonalGenerator_trace d)
      (LieProof.offDiagonalGenerator_commutator K hdiag)
      (Real.sqrt d * specNorm K) (((d : ℝ) - 1) / 2)
      (mul_pos (Real.sqrt_pos.mpr hdpos) hpos) hb
      (LieNormProof.norm_bound_of_entries _ _ (LieProof.offDiagonalGenerator_entry_norm K))
      (LieProof.diagonalGenerator_norm (by omega))
  rw [LieBalanceProof.balance_constant, hnormK] at hFn hGn
  refine ⟨U * F * Uᴴ, U * G * Uᴴ,
    Matrix.isHermitian_mul_mul_conjTranspose U hF,
    Matrix.isHermitian_mul_mul_conjTranspose U hG,
    ?_, ?_, LieTransportProof.commutator_transport U F G H hU hFG, ?_, ?_⟩
  · rw [Matrix.trace_mul_cycle, show Uᴴ * U = 1 from hU.1, Matrix.one_mul, htrF]
  · rw [Matrix.trace_mul_cycle, show Uᴴ * U = 1 from hU.1, Matrix.one_mul, htrG]
  · rwa [LieTransportProof.specNorm_unitary_conjugate U F hU]
  · rwa [LieTransportProof.specNorm_unitary_conjugate U G hU]

end SKAlgorithm.Qudit


open QAlgorithms NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

/-! The local remainder and commutator estimates adapt the actual accepted proof of
QAlgorithms.Childs.su2_small_commutator_factorization (submission
de0f1e97-d1de-4bb6-909b-7d68a2561cde) from Fin 2 to arbitrary nonempty Fin d.
All proofs are included here; no theorem from that development is imported. -/

namespace SKAlgorithm.Qudit.ExpCommutatorProof

variable {d : ℕ} [Nonempty (Fin d)]

lemma exp_remainder (X : Matrix (Fin d) (Fin d) ℂ) (hX : ‖X‖ ≤ 1) :
    ‖NormedSpace.exp X - 1 - X‖ ≤ ‖X‖ ^ 2 := by
  have hs := (hasSum_nat_add_iff' 2).mpr (exp_series_hasSum_exp' (𝕂 := ℝ) X)
  have ht := (hasSum_nat_add_iff' 2).mpr (exp_series_hasSum_exp' (𝕂 := ℝ) ‖X‖)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one,
    pow_zero, pow_one, one_smul] at hs ht
  have hb : ‖NormedSpace.exp X - (1 + X)‖ ≤ NormedSpace.exp ‖X‖ - (1 + ‖X‖) := by
    apply hs.norm_le_of_bounded ht
    intro n
    simp only [norm_smul, norm_inv, Real.norm_natCast, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le X (n + 2)) (by positivity)
  have hr := Real.norm_exp_sub_one_sub_id_le (x := ‖X‖) (by simpa using hX)
  rw [Real.exp_eq_exp_ℝ] at hr
  calc
    _ = ‖NormedSpace.exp X - (1 + X)‖ := by congr 1; abel
    _ ≤ NormedSpace.exp ‖X‖ - (1 + ‖X‖) := hb
    _ ≤ ‖NormedSpace.exp ‖X‖ - 1 - ‖X‖‖ := by
      simpa only [Real.norm_eq_abs, sub_add_eq_sub_sub] using
        (le_abs_self (NormedSpace.exp ‖X‖ - 1 - ‖X‖))
    _ ≤ ‖X‖ ^ 2 := by simpa using hr

lemma exp_distance (X : Matrix (Fin d) (Fin d) ℂ) (hX : ‖X‖ ≤ 1) :
    ‖NormedSpace.exp X - 1‖ ≤ ‖X‖ + ‖X‖ ^ 2 := by
  calc
    _ = ‖X + (NormedSpace.exp X - 1 - X)‖ := by congr 1; abel
    _ ≤ ‖X‖ + ‖NormedSpace.exp X - 1 - X‖ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl (exp_remainder X hX)

omit [Nonempty (Fin d)] in
lemma bracket_bound (X Y : Matrix (Fin d) (Fin d) ℂ) :
    ‖X * Y - Y * X‖ ≤ 2 * ‖X‖ * ‖Y‖ := by
  calc
    _ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
    _ ≤ ‖X‖ * ‖Y‖ + ‖Y‖ * ‖X‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

lemma exp_commutator_error (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1 / 2)
    (X Y : Matrix (Fin d) (Fin d) ℂ) (hX : ‖X‖ ≤ r) (hY : ‖Y‖ ≤ r)
    (hU : NormedSpace.exp X ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (hV : NormedSpace.exp Y ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    ‖NormedSpace.exp (X * Y - Y * X) - NormedSpace.exp X * NormedSpace.exp Y * star (NormedSpace.exp X) * star (NormedSpace.exp Y)‖ ≤
      18 * r ^ 3 := by
  let U := NormedSpace.exp X
  let V := NormedSpace.exp Y
  let E := U - 1 - X
  let F := V - 1 - Y
  let W := X * Y - Y * X
  have hrle : r ≤ 1 := by linarith
  have he : ‖E‖ ≤ r ^ 2 := (exp_remainder X (hX.trans hrle)).trans (by gcongr)
  have hf : ‖F‖ ≤ r ^ 2 := (exp_remainder Y (hY.trans hrle)).trans (by gcongr)
  have hu : ‖U - 1‖ ≤ 2 * r := by
    calc
      _ ≤ ‖X‖ + ‖X‖ ^ 2 := exp_distance X (hX.trans hrle)
      _ ≤ r + r ^ 2 := by gcongr
      _ ≤ 2 * r := by nlinarith
  have hv : ‖V - 1‖ ≤ 2 * r := by
    calc
      _ ≤ ‖Y‖ + ‖Y‖ ^ 2 := exp_distance Y (hY.trans hrle)
      _ ≤ r + r ^ 2 := by gcongr
      _ ≤ 2 * r := by nlinarith
  have hw : ‖W‖ ≤ 2 * r ^ 2 := by
    calc
      _ ≤ 2 * ‖X‖ * ‖Y‖ := bracket_bound X Y
      _ ≤ 2 * r * r := by gcongr
      _ = _ := by ring
  have hr4 : r ^ 4 ≤ r ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg hr 3) (sub_nonneg.mpr hrle)]
  have hd : ‖U * V - V * U - W‖ ≤ 6 * r ^ 3 := by
    have hid : U * V - V * U - W =
        (X * F - F * X) + (E * Y - Y * E) + (E * F - F * E) := by
      dsimp [E, F, W]
      noncomm_ring
    rw [hid]
    calc
      _ ≤ ‖X * F - F * X‖ + ‖E * Y - Y * E‖ + ‖E * F - F * E‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 2 * ‖X‖ * ‖F‖ + 2 * ‖E‖ * ‖Y‖ + 2 * ‖E‖ * ‖F‖ := by
        exact add_le_add (add_le_add (bracket_bound X F) (bracket_bound E Y)) (bracket_bound E F)
      _ ≤ 2 * r * r ^ 2 + 2 * r ^ 2 * r + 2 * r ^ 2 * r ^ 2 := by gcongr
      _ ≤ 6 * r ^ 3 := by nlinarith
  have hs : ‖star U * star V - 1‖ ≤ 4 * r := by
    calc
      _ = ‖star U * (star V - 1) + (star U - 1)‖ := by congr 1; noncomm_ring
      _ ≤ ‖star U * (star V - 1)‖ + ‖star U - 1‖ := norm_add_le _ _
      _ = ‖V - 1‖ + ‖U - 1‖ := by
        rw [CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hU)]
        rw [show star V - 1 = star (V - 1) by simp,
          show star U - 1 = star (U - 1) by simp, norm_star, norm_star]
      _ ≤ 4 * r := by linarith
  have hc : ‖U * V * star U * star V - 1 - W‖ ≤ 14 * r ^ 3 := by
    have hid : U * V * star U * star V - 1 - W =
        (U * V - V * U - W) * star U * star V + W * (star U * star V - 1) := by
      have hvu : V * U * star U * star V = 1 := by
        rw [mul_assoc V U (star U), hU.2, mul_one, hV.2]
      calc
        _ = U * V * star U * star V - V * U * star U * star V - W := by rw [hvu]
        _ = _ := by noncomm_ring
    rw [hid]
    calc
      _ ≤ ‖(U * V - V * U - W) * star U * star V‖ + ‖W * (star U * star V - 1)‖ := norm_add_le _ _
      _ = ‖U * V - V * U - W‖ + ‖W * (star U * star V - 1)‖ := by
        rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hV),
          CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU)]
      _ ≤ 6 * r ^ 3 + (2 * r ^ 2) * (4 * r) := by
        exact add_le_add hd ((norm_mul_le _ _).trans (mul_le_mul hw hs (norm_nonneg _) (by positivity)))
      _ = 14 * r ^ 3 := by ring
  have hew : ‖NormedSpace.exp W - 1 - W‖ ≤ 4 * r ^ 3 := by
    calc
      _ ≤ ‖W‖ ^ 2 := exp_remainder W (hw.trans (by nlinarith))
      _ ≤ (2 * r ^ 2) ^ 2 := by gcongr
      _ ≤ 4 * r ^ 3 := by nlinarith
  calc
    _ = ‖(NormedSpace.exp W - 1 - W) - (U * V * star U * star V - 1 - W)‖ := by
      dsimp [W, U, V]
      congr 1
      abel
    _ ≤ ‖NormedSpace.exp W - 1 - W‖ + ‖U * V * star U * star V - 1 - W‖ := norm_sub_le _ _
    _ ≤ 4 * r ^ 3 + 14 * r ^ 3 := add_le_add hew hc
    _ = _ := by ring


end SKAlgorithm.Qudit.ExpCommutatorProof

open SKAlgorithm.Qudit.ExpCommutatorProof

theorem sk5_exp_bound :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (d : ℕ) (F G : Matrix (Fin d) (Fin d) ℂ) (δ : ℝ),
        F.IsHermitian → G.IsHermitian →
        specNorm F < δ → specNorm G < δ →
        specNorm
          (NormedSpace.exp (Complex.I • F) *
           NormedSpace.exp (Complex.I • G) *
           NormedSpace.exp ((-Complex.I) • F) *
           NormedSpace.exp ((-Complex.I) • G) -
           NormedSpace.exp (Complex.I • (Complex.I • (F * G - G * F)))) ≤
          c₁ * δ ^ 3 := by
  refine ⟨18, by norm_num, ?_⟩
  intro d F G δ hF hG hFn hGn
  change ‖F‖ < δ at hFn
  change ‖G‖ < δ at hGn
  change ‖_‖ ≤ _
  have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg F) hFn
  by_cases hd : d = 0
  · subst d
    have hz :
        NormedSpace.exp (Complex.I • F) * NormedSpace.exp (Complex.I • G) * NormedSpace.exp ((-Complex.I) • F) *
          NormedSpace.exp ((-Complex.I) • G) - NormedSpace.exp (Complex.I • (Complex.I • (F * G - G * F))) = 0 :=
      Subsingleton.elim _ _
    rw [hz, norm_zero]
    positivity
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := .restrictScalars ℚ ℂ _
  let X := Complex.I • F
  let Y := Complex.I • G
  have hX : ‖X‖ ≤ δ := by simpa [X, norm_smul] using hFn.le
  have hY : ‖Y‖ ≤ δ := by simpa [Y, norm_smul] using hGn.le
  have hXs : X ∈ skewAdjoint (Matrix (Fin d) (Fin d) ℂ) :=
    hF.isSelfAdjoint.smul_mem_skewAdjoint Complex.conj_I
  have hYs : Y ∈ skewAdjoint (Matrix (Fin d) (Fin d) ℂ) :=
    hG.isSelfAdjoint.smul_mem_skewAdjoint Complex.conj_I
  have hU := exp_mem_unitary_of_mem_skewAdjoint hXs
  have hV := exp_mem_unitary_of_mem_skewAdjoint hYs
  have hstarX : star (NormedSpace.exp X) = NormedSpace.exp ((-Complex.I) • F) := by
    rw [star_exp, skewAdjoint.mem_iff.mp hXs]
    simp [X]
  have hstarY : star (NormedSpace.exp Y) = NormedSpace.exp ((-Complex.I) • G) := by
    rw [star_exp, skewAdjoint.mem_iff.mp hYs]
    simp [Y]
  have hbracket : X * Y - Y * X = Complex.I • (Complex.I • (F * G - G * F)) := by
    simp [X, Y, smul_smul, smul_sub]
  have hWs : X * Y - Y * X ∈ skewAdjoint (Matrix (Fin d) (Fin d) ℂ) := by
    rw [skewAdjoint.mem_iff]
    simp [star_sub, star_mul, skewAdjoint.mem_iff.mp hXs, skewAdjoint.mem_iff.mp hYs]
  have hW := exp_mem_unitary_of_mem_skewAdjoint hWs
  rw [← hbracket, ← hstarX, ← hstarY]
  change ‖NormedSpace.exp X * NormedSpace.exp Y * star (NormedSpace.exp X) * star (NormedSpace.exp Y) - NormedSpace.exp (X * Y - Y * X)‖ ≤ _
  by_cases hsmall : δ ≤ 1 / 2
  · rw [norm_sub_rev]
    exact exp_commutator_error δ hδ.le hsmall X Y hX hY hU hV
  · have hprod : NormedSpace.exp X * NormedSpace.exp Y * star (NormedSpace.exp X) * star (NormedSpace.exp Y) ∈
        unitary (Matrix (Fin d) (Fin d) ℂ) :=
      mul_mem (mul_mem (mul_mem hU hV) (Unitary.star_mem hU)) (Unitary.star_mem hV)
    calc
      _ ≤ ‖NormedSpace.exp X * NormedSpace.exp Y * star (NormedSpace.exp X) * star (NormedSpace.exp Y)‖ + ‖NormedSpace.exp (X * Y - Y * X)‖ :=
        norm_sub_le _ _
      _ = 2 := by rw [CStarRing.norm_of_mem_unitary hprod, CStarRing.norm_of_mem_unitary hW]; norm_num
      _ ≤ 18 * δ ^ 3 := by
        have hhalf : 1 / 2 ≤ δ := le_of_lt (lt_of_not_ge hsmall)
        nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf,
          mul_nonneg (sub_nonneg.mpr hhalf) (sq_nonneg δ)]

namespace SKAlgorithm.Qudit.GroupApproxProof

lemma exp_I_unitary {d : ℕ} (F : Matrix (Fin d) (Fin d) ℂ) (hF : F.IsHermitian) :
    NormedSpace.exp (Complex.I • F) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := .restrictScalars ℚ ℂ _
  exact exp_mem_unitary_of_mem_skewAdjoint
    (hF.isSelfAdjoint.smul_mem_skewAdjoint Complex.conj_I)

lemma exp_I_distance {d : ℕ} (F : Matrix (Fin d) (Fin d) ℂ) (hF : F.IsHermitian) :
    specNorm (1 - NormedSpace.exp (Complex.I • F)) ≤ 2 * specNorm F := by
  change ‖1 - NormedSpace.exp (Complex.I • F)‖ ≤ 2 * ‖F‖
  by_cases hd : d = 0
  · subst d
    have hz : F = 0 := Subsingleton.elim _ _
    simp [hz]
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
  by_cases hf : ‖F‖ ≤ 1
  · rw [norm_sub_rev]
    calc
      _ ≤ ‖Complex.I • F‖ + ‖Complex.I • F‖ ^ 2 :=
        ExpCommutatorProof.exp_distance _ (by simpa [norm_smul] using hf)
      _ = ‖F‖ + ‖F‖ ^ 2 := by simp [norm_smul]
      _ ≤ 2 * ‖F‖ := by nlinarith [norm_nonneg F]
  · calc
      _ ≤ ‖(1 : Matrix (Fin d) (Fin d) ℂ)‖ + ‖NormedSpace.exp (Complex.I • F)‖ :=
        norm_sub_le _ _
      _ = 2 := by rw [norm_one, CStarRing.norm_of_mem_unitary (exp_I_unitary F hF)]; norm_num
      _ ≤ 2 * ‖F‖ := by linarith

end SKAlgorithm.Qudit.GroupApproxProof


open Matrix Complex NormedSpace Filter
open scoped Matrix.Norms.L2Operator Topology
open QAlgorithms

namespace SKAlgorithm.Qudit.LogProof

lemma exp_diagonal {d : ℕ} (z : Fin d → ℂ) :
    NormedSpace.exp (Matrix.diagonal z) = Matrix.diagonal (fun i => Complex.exp (z i)) := by
  have h := NormedSpace.map_exp (Matrix.diagonalRingHom (Fin d) ℂ)
    (by change Continuous (Matrix.diagonal : (Fin d → ℂ) → Matrix (Fin d) (Fin d) ℂ); fun_prop) z
  simpa only [Matrix.diagonalRingHom_apply, Pi.exp_def, Complex.exp_eq_exp_ℂ] using h.symm

lemma det_conj_unitary {d : ℕ} (V : Matrix.unitaryGroup (Fin d) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    ((V : Matrix (Fin d) (Fin d) ℂ) * A * star (V : Matrix (Fin d) (Fin d) ℂ)).det = A.det := by
  have hv := congrArg Matrix.det (Unitary.coe_mul_star_self V)
  rw [Matrix.det_mul, Matrix.det_one] at hv
  change (V : Matrix (Fin d) (Fin d) ℂ).det * (star (V : Matrix (Fin d) (Fin d) ℂ)).det = 1 at hv
  rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, hv, one_mul]

set_option backward.isDefEq.respectTransparency false in
lemma det_exp_smul_I {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    (NormedSpace.exp (Complex.I • H)).det = Complex.exp (Complex.I * H.trace) := by
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  let V := hH.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) V
  let z : Fin d → ℂ := fun j => Complex.I * (hH.eigenvalues j : ℂ)
  have hs : Complex.I • H = φ (Matrix.diagonal z) := by
    rw [hH.spectral_theorem]
    change Complex.I • φ (Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ))) = _
    rw [← map_smul]
    congr 1
    ext i j
    simp [z, Matrix.diagonal, mul_ite]
  have hc : Continuous φ := by
    change Continuous (fun A : Matrix (Fin d) (Fin d) ℂ =>
      (V : Matrix (Fin d) (Fin d) ℂ) * A * star (V : Matrix (Fin d) (Fin d) ℂ))
    fun_prop
  rw [hs, ← NormedSpace.map_exp φ hc, exp_diagonal]
  change ((V : Matrix (Fin d) (Fin d) ℂ) * _ * star (V : Matrix (Fin d) (Fin d) ℂ)).det = _
  rw [det_conj_unitary, Matrix.det_diagonal, ← Complex.exp_sum,
    hH.trace_eq_sum_eigenvalues, Finset.mul_sum]
  rfl

lemma arg_one {d : ℕ} :
    Unitary.argSelfAdjoint (1 : Matrix.unitaryGroup (Fin d) ℂ) = 0 := by
  simpa using (argSelfAdjoint_expUnitary (x := (0 : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)))
    (by simpa using Real.pi_pos))

lemma exists_small_arg_radius (d : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : Matrix.unitaryGroup (Fin d) ℂ,
      ‖(u : Matrix (Fin d) (Fin d) ℂ) - 1‖ < ε →
      ‖Unitary.argSelfAdjoint u‖ < 1 ∧
      ‖Matrix.trace (Unitary.argSelfAdjoint u : Matrix (Fin d) (Fin d) ℂ)‖ < 1 := by
  have hc : ContinuousAt (Unitary.argSelfAdjoint :
      Matrix.unitaryGroup (Fin d) ℂ → selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) 1 :=
    Unitary.continuousOn_argSelfAdjoint.continuousAt
      (Metric.isOpen_ball.mem_nhds (by simp))
  have ht : ContinuousAt (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
      Matrix.trace (Unitary.argSelfAdjoint u : Matrix (Fin d) (Fin d) ℂ)) 1 := by
    have hc' : ContinuousAt (fun u : Matrix.unitaryGroup (Fin d) ℂ =>
        (Unitary.argSelfAdjoint u : Matrix (Fin d) (Fin d) ℂ)) 1 :=
      continuous_subtype_val.continuousAt.comp hc
    have ht' : Continuous (Matrix.trace : Matrix (Fin d) (Fin d) ℂ → ℂ) := by
      unfold Matrix.trace Matrix.diag
      fun_prop
    exact ht'.continuousAt.comp hc' 
  have hn : ∀ᶠ u : Matrix.unitaryGroup (Fin d) ℂ in 𝓝 1,
      ‖Unitary.argSelfAdjoint u‖ < 1 :=
    hc.norm.eventually (gt_mem_nhds (by simp [arg_one]))
  have htn : ∀ᶠ u : Matrix.unitaryGroup (Fin d) ℂ in 𝓝 1,
      ‖Matrix.trace (Unitary.argSelfAdjoint u : Matrix (Fin d) (Fin d) ℂ)‖ < 1 :=
    ht.norm.eventually (gt_mem_nhds (by simp [arg_one]))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp (hn.and htn)
  refine ⟨ε, hε, fun u hu => he ?_⟩
  simpa only [Subtype.dist_eq, OneMemClass.coe_one, dist_eq_norm] using hu

lemma trace_zero_of_exp_det_one {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ)
    (hH : H.IsHermitian) (ht : ‖H.trace‖ < 1)
    (he : (NormedSpace.exp (Complex.I • H)).det = 1) : H.trace = 0 := by
  rw [det_exp_smul_I H hH] at he
  have him : |(Complex.I * H.trace).im| < Real.pi := by
    calc
      _ ≤ ‖Complex.I * H.trace‖ := Complex.abs_im_le_norm _
      _ = ‖H.trace‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ < 1 := ht
      _ < Real.pi := by linarith [Real.pi_gt_three]
  have hz : Complex.I * H.trace = 0 :=
    Complex.exp_inj_of_neg_pi_lt_of_le_pi (abs_lt.mp him).1 (abs_lt.mp him).2.le
      (by simpa using neg_neg_of_pos Real.pi_pos) (by simpa using Real.pi_pos.le)
      (by simpa only [Complex.exp_zero] using he)
  exact (mul_eq_zero.mp hz).resolve_left Complex.I_ne_zero

lemma exists_local_chart (d : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ U : SU d, opDist 1 U < ε →
      ∃ H : Matrix (Fin d) (Fin d) ℂ, H.IsHermitian ∧ H.trace = 0 ∧ specNorm H < 1 ∧
        (U : Matrix (Fin d) (Fin d) ℂ) = NormedSpace.exp (Complex.I • H) ∧
        (opDist 1 U)^2 = 2 * (1 - Real.cos (specNorm H)) := by
  obtain ⟨ε, hε, he⟩ := exists_small_arg_radius d
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro U hU
  let u : Matrix.unitaryGroup (Fin d) ℂ := ⟨U, U.property.1⟩
  have hdist : ‖(u : Matrix (Fin d) (Fin d) ℂ) - 1‖ = opDist 1 U := by
    change ‖(U : Matrix (Fin d) (Fin d) ℂ) - 1‖ = ‖1 - (U : Matrix (Fin d) (Fin d) ℂ)‖
    exact norm_sub_rev _ _
  have hu : ‖(u : Matrix (Fin d) (Fin d) ℂ) - 1‖ < 2 := by
    rw [hdist]
    exact (hU.trans_le (min_le_right _ _)).trans (by norm_num)
  obtain ⟨hn, ht⟩ := he u (by rw [hdist]; exact hU.trans_le (min_le_left _ _))
  let H : Matrix (Fin d) (Fin d) ℂ := Unitary.argSelfAdjoint u
  have hH : H.IsHermitian := (Unitary.argSelfAdjoint u).property.isHermitian
  have hexp : (U : Matrix (Fin d) (Fin d) ℂ) = NormedSpace.exp (Complex.I • H) := by
    have h := congrArg Subtype.val (expUnitary_argSelfAdjoint hu)
    exact h.symm
  refine ⟨H, hH, trace_zero_of_exp_det_one H hH ht ?_, hn, hexp, ?_⟩
  · rw [← hexp]
    exact U.property.2
  · have hc := Unitary.two_mul_one_sub_cos_norm_argSelfAdjoint hu
    rw [hdist] at hc
    exact hc.symm

end SKAlgorithm.Qudit.LogProof


namespace SKAlgorithm.Qudit.ScalarProof

/-- The nonnegative chord length is twice the sine of the half-angle. -/
theorem chord_eq_two_sin_half {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hsq : s ^ 2 = 2 * (1 - Real.cos t)) :
    s = 2 * Real.sin (t / 2) := by
  have hsin : 0 ≤ Real.sin (t / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_gt_three])
  apply (sq_eq_sq₀ hs (mul_nonneg (by norm_num) hsin)).mp
  have hhalf := Real.sin_sq_eq_half_sub (x := t / 2)
  rw [show 2 * (t / 2) = t by ring] at hhalf
  nlinarith

/-- A quantitative angle/chord comparison with the Taylor constant `1/24`. -/
theorem chord_cubic_bound {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hsq : s ^ 2 = 2 * (1 - Real.cos t)) :
    |s - t| ≤ t ^ 3 / 24 := by
  have heq := chord_eq_two_sin_half ht ht1 hs hsq
  have hb := Real.abs_sub_sin_le (t / 2)
  rw [abs_of_nonneg (show 0 ≤ t / 2 by linarith)] at hb
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The same comparison in the square-root formulation. -/
theorem sqrt_chord_cubic_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |Real.sqrt (2 * (1 - Real.cos t)) - t| ≤ t ^ 3 / 24 :=
  chord_cubic_bound ht ht1 (Real.sqrt_nonneg _)
    (Real.sq_sqrt (by nlinarith [Real.cos_le_one t]))

/-- A convenient linear inverse estimate on the same chart. -/
theorem angle_le_twice_chord {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hsq : s ^ 2 = 2 * (1 - Real.cos t)) :
    t ≤ 2 * s := by
  have hb := (abs_le.mp (chord_cubic_bound ht ht1 hs hsq)).1
  have hcube : t ^ 3 ≤ t := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1),
      mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht1)]
  nlinarith

end SKAlgorithm.Qudit.ScalarProof

namespace SKAlgorithm.Qudit.GroupApproxProof

noncomputable def expSU {d : ℕ} (F : Matrix (Fin d) (Fin d) ℂ)
    (hF : F.IsHermitian) (htr : F.trace = 0) : SU d :=
  ⟨NormedSpace.exp (Complex.I • F), exp_I_unitary F hF, by
    change (NormedSpace.exp (Complex.I • F)).det = 1
    rw [LogProof.det_exp_smul_I F hF, htr, mul_zero, Complex.exp_zero]⟩

lemma expSU_coe {d : ℕ} (F : Matrix (Fin d) (Fin d) ℂ)
    (hF : F.IsHermitian) (htr : F.trace = 0) :
    (expSU F hF htr : Matrix (Fin d) (Fin d) ℂ) = NormedSpace.exp (Complex.I • F) := rfl

lemma expSU_inv_coe {d : ℕ} (F : Matrix (Fin d) (Fin d) ℂ)
    (hF : F.IsHermitian) (htr : F.trace = 0) :
    (((expSU F hF htr)⁻¹ : SU d) : Matrix (Fin d) (Fin d) ℂ) =
      NormedSpace.exp ((-Complex.I) • F) := by
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := .restrictScalars ℚ ℂ _
  change star (NormedSpace.exp (Complex.I • F)) = _
  rw [star_exp]
  congr 1
  have hs := hF.isSelfAdjoint.smul_mem_skewAdjoint Complex.conj_I
  rw [skewAdjoint.mem_iff.mp hs]
  simp

lemma sqrt_cube (ε : ℝ) (he : 0 < ε) :
    (Real.sqrt ε) ^ 3 = ε ^ ((3 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul he.le]
  norm_num

lemma rpow_three_halves (ε : ℝ) (he : 0 < ε) :
    ε ^ ((3 : ℝ) / 2) = ε * Real.sqrt ε := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add he, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

end SKAlgorithm.Qudit.GroupApproxProof

open SKAlgorithm.Qudit
open SKAlgorithm.Qudit.GroupApproxProof

theorem solution (d : ℕ) :
    ∃ c' c'' : ℝ, 0 < c' ∧ 0 < c'' ∧ ∀ ε : ℝ, 0 < ε → ∀ U : SU d, opDist 1 U < ε →
      ∃ V W : SU d, opDist (V * W * V⁻¹ * W⁻¹) U < c' * ε ^ ((3 : ℝ) / 2) ∧
        opDist 1 V < c'' * Real.sqrt ε ∧ opDist 1 W < c'' * Real.sqrt ε := by
  obtain ⟨r, hr, hchart⟩ := LogProof.exists_local_chart d
  obtain ⟨c₁, hc₁, hexpbound⟩ := sk5_exp_bound
  let A : ℝ := (d : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (((d : ℝ) - 1) / 2)
  let k : ℝ := 2 * A + 1
  let c' : ℝ := c₁ * k ^ 3 + 1 + 1 / Real.sqrt r
  let c'' : ℝ := 2 * k
  have hA : 0 ≤ A := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (Real.sqrt_nonneg _)
  have hk : 0 < k := by dsimp [k]; linarith
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hcp : 0 < c' := by dsimp [c']; positivity
  have hcpp : 0 < c'' := by dsimp [c'']; positivity
  refine ⟨c', c'', hcp, hcpp, ?_⟩
  intro ε hε U hU
  have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hp : 0 < ε ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hε _
  by_cases hsmall : ε < r
  · obtain ⟨H, hH, htr, hn1, heH, hcos⟩ := hchart U (hU.trans hsmall)
    have hn : specNorm H ≤ 2 * opDist 1 U :=
      ScalarProof.angle_le_twice_chord (LieNormProof.specNorm_nonneg H) hn1.le
        (by exact norm_nonneg _) hcos
    have hnsqrt : Real.sqrt (specNorm H) ≤ 2 * Real.sqrt ε := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      have hn' := hn.trans (mul_le_mul_of_nonneg_left hU.le (by norm_num : (0 : ℝ) ≤ 2))
      nlinarith [Real.sq_sqrt hε.le]
    obtain ⟨F, G, hF, hG, htF, htG, hFG, hFn, hGn⟩ :=
      SKAlgorithm.Qudit.balanced_traceless (-H) hH.neg (by simp [htr])
    have hnneg : specNorm (-H) = specNorm H := norm_neg H
    rw [hnneg] at hFn hGn
    have hFbound : specNorm F < k * Real.sqrt ε := by
      calc
        _ ≤ A * Real.sqrt (specNorm H) := hFn
        _ ≤ A * (2 * Real.sqrt ε) := mul_le_mul_of_nonneg_left hnsqrt hA
        _ < k * Real.sqrt ε := by dsimp [k]; nlinarith
    have hGbound : specNorm G < k * Real.sqrt ε := by
      calc
        _ ≤ A * Real.sqrt (specNorm H) := hGn
        _ ≤ A * (2 * Real.sqrt ε) := mul_le_mul_of_nonneg_left hnsqrt hA
        _ < k * Real.sqrt ε := by dsimp [k]; nlinarith
    let V := expSU F hF htF
    let W := expSU G hG htG
    have htarget : Complex.I • (Complex.I • (F * G - G * F)) = Complex.I • H := by
      rw [hFG]
      simp [smul_smul]
    have hprod : ((V * W * V⁻¹ * W⁻¹ : SU d) : Matrix (Fin d) (Fin d) ℂ) =
        NormedSpace.exp (Complex.I • F) * NormedSpace.exp (Complex.I • G) *
          NormedSpace.exp ((-Complex.I) • F) * NormedSpace.exp ((-Complex.I) • G) := by
      change (V : Matrix (Fin d) (Fin d) ℂ) * W * (V⁻¹ : SU d) * (W⁻¹ : SU d) = _
      rw [expSU_inv_coe F hF htF, expSU_inv_coe G hG htG]
      rfl
    refine ⟨V, W, ?_, ?_, ?_⟩
    · have hb := hexpbound d F G (k * Real.sqrt ε) hF hG hFbound hGbound
      rw [htarget, mul_pow, sqrt_cube ε hε] at hb
      have hcoef : c₁ * k ^ 3 < c' := by
        dsimp [c']
        have hinv : 0 < 1 / Real.sqrt r := one_div_pos.mpr hsr
        linarith
      unfold opDist
      rw [hprod, heH]
      calc
        _ ≤ c₁ * (k ^ 3 * ε ^ ((3 : ℝ) / 2)) := hb
        _ = (c₁ * k ^ 3) * ε ^ ((3 : ℝ) / 2) := by ring
        _ < c' * ε ^ ((3 : ℝ) / 2) := mul_lt_mul_of_pos_right hcoef hp
    · change specNorm (1 - NormedSpace.exp (Complex.I • F)) < _
      calc
        _ ≤ 2 * specNorm F := exp_I_distance F hF
        _ < 2 * (k * Real.sqrt ε) := mul_lt_mul_of_pos_left hFbound (by norm_num)
        _ = c'' * Real.sqrt ε := by dsimp [c'']; ring
    · change specNorm (1 - NormedSpace.exp (Complex.I • G)) < _
      calc
        _ ≤ 2 * specNorm G := exp_I_distance G hG
        _ < 2 * (k * Real.sqrt ε) := mul_lt_mul_of_pos_left hGbound (by norm_num)
        _ = c'' * Real.sqrt ε := by dsimp [c'']; ring
  · have hroot : Real.sqrt r ≤ Real.sqrt ε := Real.sqrt_le_sqrt (le_of_not_gt hsmall)
    have hcpge : 1 / Real.sqrt r ≤ c' := by
      dsimp [c']
      have hpos : 0 ≤ c₁ * k ^ 3 := mul_nonneg hc₁.le (pow_nonneg hk.le _)
      linarith
    have hfactor : 1 ≤ c' * Real.sqrt ε := by
      calc
        1 ≤ (1 / Real.sqrt r) * Real.sqrt ε := by
          rw [one_div, mul_comm, ← div_eq_mul_inv]
          exact (one_le_div hsr).mpr hroot
        _ ≤ c' * Real.sqrt ε := mul_le_mul_of_nonneg_right hcpge hsqrt.le
    have hscale : ε ≤ c' * ε ^ ((3 : ℝ) / 2) := by
      rw [rpow_three_halves ε hε]
      nlinarith [mul_le_mul_of_nonneg_left hfactor hε.le]
    refine ⟨1, 1, ?_, ?_, ?_⟩
    · simpa using hU.trans_le hscale
    · change specNorm (1 - (1 : Matrix (Fin d) (Fin d) ℂ)) < _
      simp only [sub_self, specNorm, norm_zero]
      exact mul_pos hcpp hsqrt
    · change specNorm (1 - (1 : Matrix (Fin d) (Fin d) ℂ)) < _
      simp only [sub_self, specNorm, norm_zero]
      exact mul_pos hcpp hsqrt
