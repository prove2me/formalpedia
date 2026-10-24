-- Prove2me | solution 1 for SKAlgorithm.Qudit.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:27:29.449445+00:00
-- url     : https://prove2.me/submissions/4c68475a-53dd-49ef-9863-c5861e192563

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


open SKAlgorithm.Qudit

theorem solution {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (htr : H.trace = 0) :
    ∃ F G : Matrix (Fin d) (Fin d) ℂ, F.IsHermitian ∧ G.IsHermitian ∧
      F * G - G * F = Complex.I • H ∧
      specNorm F ≤ (d : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (((d : ℝ) - 1) / 2) * Real.sqrt (specNorm H) ∧
      specNorm G ≤ (d : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (((d : ℝ) - 1) / 2) * Real.sqrt (specNorm H) := by
  classical
  by_cases hzero : H = 0
  · subst H
    refine ⟨0, 0, Matrix.isHermitian_zero, Matrix.isHermitian_zero, by simp, ?_, ?_⟩ <;>
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
  obtain ⟨F, G, hF, hG, hFG, hFn, hGn⟩ :=
    LieBalanceProof.balanced_rescaling (LieProof.offDiagonalGenerator K)
      (LieProof.diagonalGenerator d) K
      (LieProof.offDiagonalGenerator_hermitian K hK)
      (LieProof.diagonalGenerator_hermitian d)
      (LieProof.offDiagonalGenerator_commutator K hdiag)
      (Real.sqrt d * specNorm K) (((d : ℝ) - 1) / 2)
      (mul_pos (Real.sqrt_pos.mpr hdpos) hpos) hb
      (LieNormProof.norm_bound_of_entries _ _ (LieProof.offDiagonalGenerator_entry_norm K))
      (LieProof.diagonalGenerator_norm (by omega))
  rw [LieBalanceProof.balance_constant, hnormK] at hFn hGn
  refine ⟨U * F * Uᴴ, U * G * Uᴴ,
    Matrix.isHermitian_mul_mul_conjTranspose U hF,
    Matrix.isHermitian_mul_mul_conjTranspose U hG,
    LieTransportProof.commutator_transport U F G H hU hFG, ?_, ?_⟩
  · rwa [LieTransportProof.specNorm_unitary_conjugate U F hU]
  · rwa [LieTransportProof.specNorm_unitary_conjugate U G hU]
