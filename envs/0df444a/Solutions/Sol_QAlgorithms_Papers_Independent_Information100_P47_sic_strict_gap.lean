-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P47.sic_strict_gap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:32:02.573991+00:00
-- url     : https://prove2.me/submissions/cdf673dc-3957-456d-87e9-e89c7e6cfcb6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P47

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Matrix ComplexOrder

namespace X6P47X

open QAlgorithms.Papers.Independent.Information100.P47 hiding spectralNorm

local notation "SN" => QAlgorithms.Papers.Independent.Information100.P47.spectralNorm
local notation "TR" => QAlgorithms.Papers.Independent.Information100.P47.trivial

/-- an entry bounds the spectral norm from below -/
theorem entry_le {d : ℕ} (X : Mat d) (i j : Fin d) :
    ENNReal.ofReal ‖X i j‖ ≤ SN X := by
  unfold QAlgorithms.Papers.Independent.Information100.P47.spectralNorm
  set v : EuclideanSpace ℂ (Fin d) := EuclideanSpace.single j 1
  have hv : ‖v‖ = 1 := by simp [v]
  refine le_trans ?_ (le_iSup _ ⟨v, hv⟩)
  apply ENNReal.ofReal_le_ofReal
  have h1 : (QAlgorithms.act X v) i = X i j := by
    simp [QAlgorithms.act, v]
  rw [← h1]
  exact PiLp.norm_apply_le _ i

/-- conjugation by a unitary does not increase the spectral norm -/
theorem conj_le {d : ℕ} (U Y : Mat d) (hU : IsUnitary U) :
    SN (Uᴴ * Y * U) ≤ SN Y := by
  unfold QAlgorithms.Papers.Independent.Information100.P47.spectralNorm
  refine iSup_le fun v => ?_
  set w : EuclideanSpace ℂ (Fin d) := QAlgorithms.act U v.val
  have hiso : ∀ (W : Mat d), Wᴴ * W = 1 → ∀ u : EuclideanSpace ℂ (Fin d),
      ‖QAlgorithms.act W u‖ = ‖u‖ := by
    intro W hW u
    have key : (W *ᵥ WithLp.ofLp u) ⬝ᵥ star (W *ᵥ WithLp.ofLp u) =
        WithLp.ofLp u ⬝ᵥ star (WithLp.ofLp u) := by
      rw [Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        hW, Matrix.one_mulVec, dotProduct_comm]
    have h2 : ‖QAlgorithms.act W u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ]
      simp only [EuclideanSpace.inner_eq_star_dotProduct, QAlgorithms.act, WithLp.ofLp_toLp]
      rw [key]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hw : ‖w‖ = 1 := by rw [hiso U hU.1, v.2]
  refine le_trans ?_ (le_iSup _ ⟨w, hw⟩)
  apply ENNReal.ofReal_le_ofReal
  have : QAlgorithms.act (Uᴴ * Y * U) v.val = QAlgorithms.act Uᴴ (QAlgorithms.act Y w) := by
    simp [QAlgorithms.act, w, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [this, hiso Uᴴ (by rw [Matrix.conjTranspose_conjTranspose]; exact hU.2)]


theorem hn (z : ℂ) (h1 : z.re ^ 2 = 1) (h2 : z.im ^ 2 = 1) : |√2|⁻¹ * ‖z‖ = 1 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, h1, h2, abs_of_pos (by positivity)]
  norm_num

theorem diag_entries : ∀ x : Fin 4, xyPOVM x 0 0 = 1/4 ∧ xyPOVM x 1 1 = 1/4 := by
  intro x; fin_cases x <;> simp [xyPOVM, sigmaX, sigmaY]

theorem off_entries : ∀ x : Fin 4, ‖xyPOVM x 0 1‖ = 1/4 ∧ ‖xyPOVM x 1 0‖ = 1/4 := by
  intro x; fin_cases x <;> simp [xyPOVM, sigmaX, sigmaY] <;>
    exact ⟨hn _ (by simp) (by simp), hn _ (by simp) (by simp)⟩

theorem offdiag_bound (X : Mat 2) (h00 : X 0 0 = 0) (h11 : X 1 1 = 0)
    (h01 : ‖X 0 1‖ = 1/4) (h10 : ‖X 1 0‖ = 1/4) : SN X ≤ ENNReal.ofReal (1/4) := by
  unfold QAlgorithms.Papers.Independent.Information100.P47.spectralNorm
  refine iSup_le fun v => ENNReal.ofReal_le_ofReal ?_
  have hv := v.2
  have hsq : ‖QAlgorithms.act X v.val‖ ^ 2 = (1/16) * ‖v.val‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [QAlgorithms.act, Fin.sum_univ_two, PiLp.toLp_apply, Matrix.mulVec, dotProduct,
      h00, h11, zero_mul, zero_add, add_zero, norm_mul, h01, h10, mul_pow]
    ring
  rw [hv] at hsq
  have h0 : 0 ≤ ‖QAlgorithms.act X v.val‖ := norm_nonneg _
  nlinarith

end X6P47X

open scoped BigOperators ComplexConjugate ENNReal Matrix ComplexOrder

namespace X6P47S

open QAlgorithms.Papers.Independent.Information100.P47 hiding spectralNorm

local notation "SN" => QAlgorithms.Papers.Independent.Information100.P47.spectralNorm

/-! ### tight frame of a tetrahedron -/

section frame

variable (r : Fin 4 → Fin 3 → ℝ) (hr : IsTetrahedron r)
include hr

theorem gram (x y : Fin 4) : ∑ i, r x i * r y i = if x = y then 1 else -(1/3) := by
  split_ifs with h
  · subst h; simpa [sq] using hr.1 x
  · exact hr.2 x y h

theorem sum_r (i : Fin 3) : ∑ x, r x i = 0 := by
  have h : ∑ i, (∑ x, r x i) ^ 2 = 0 := by
    have : ∑ i, (∑ x, r x i) ^ 2 = ∑ x, ∑ y, ∑ i, r x i * r y i := by
      simp only [sq, Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
    rw [this]
    simp only [gram r hr]
    simp [Fin.sum_univ_four]
    norm_num
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (∑ x, r x i))).1 h i
    (Finset.mem_univ _)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

/-- K = S - 4/3 I -/
def K (i k : Fin 3) : ℝ := ∑ y, r y i * r y k - if i = k then 4/3 else 0

omit hr in
theorem K_symm (i k : Fin 3) : K r i k = K r k i := by
  unfold K
  congr 1
  · exact Finset.sum_congr rfl fun y _ => mul_comm _ _
  · by_cases h : i = k
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]

theorem K_r (x : Fin 4) (i : Fin 3) : ∑ k, K r i k * r x k = 0 := by
  unfold K
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have : ∑ k, (∑ y, r y i * r y k) * r x k = ∑ y, r y i * (∑ k, r y k * r x k) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun k _ => by ring
  rw [this]
  simp only [gram r hr, mul_ite, mul_one]
  have e : ∑ y, (if y = x then r y i else r y i * -(1/3)) =
      (4/3) * r x i - (1/3) * ∑ y, r y i := by
    have : ∀ y, (if y = x then r y i else r y i * -(1/3)) =
        r y i * -(1/3) + if y = x then (4/3) * r y i else 0 := by
      intro y; split_ifs <;> ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      ← Finset.sum_mul]
    ring
  rw [e, sum_r r hr]; ring

theorem K_sq (i j : Fin 3) : ∑ k, K r i k * K r k j = -(4/3) * K r i j := by
  have h1 : ∀ k, K r k j = (∑ y, r y k * r y j) - if k = j then 4/3 else 0 := fun k => rfl
  simp only [h1, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have : ∑ k, K r i k * ∑ y, r y k * r y j = 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun y _ => ?_
    have := K_r r hr y i
    rw [show ∑ k, K r i k * (r y k * r y j) = (∑ k, K r i k * r y k) * r y j by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring]
    rw [this, zero_mul]
  rw [this]; split_ifs <;> ring

theorem K_zero (i j : Fin 3) : K r i j = 0 := by
  have htr : ∑ i, K r i i = 0 := by
    unfold K
    simp only [if_true, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    rw [Finset.sum_comm]
    have : ∀ y, ∑ i, r y i * r y i = 1 := fun y => by simpa using gram r hr y y
    simp only [this]
    simp; norm_num
  have hsq : ∑ i, ∑ j, K r i j ^ 2 = 0 := by
    have : ∑ i, ∑ j, K r i j ^ 2 = ∑ i, ∑ j, K r i j * K r j i := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [K_symm r j i, sq]
    rw [this]
    simp only [K_sq r hr, ← Finset.mul_sum, htr, mul_zero]
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg (K r i j))).1 hsq i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (K r i j))).1 h1 j
    (Finset.mem_univ _)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2

theorem tight (n : Fin 3 → ℝ) : ∑ x, (∑ i, r x i * n i) ^ 2 = (4/3) * ∑ i, n i ^ 2 := by
  have hS : ∀ i k, ∑ y, r y i * r y k = if i = k then 4/3 else 0 := by
    intro i k
    have := K_zero r hr i k
    unfold K at this
    linarith
  have h1 : ∀ x, (∑ i, r x i * n i) ^ 2 = ∑ i, ∑ k, n i * n k * (r x i * r x k) := by
    intro x; rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have : ∑ x, (∑ i, r x i * n i) ^ 2 = ∑ i, ∑ k, n i * n k * ∑ y, r y i * r y k := by
    simp only [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [this]
  simp only [hS, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end frame

/-! ### Bloch algebra -/

theorem bloch_apply (v : Fin 3 → ℝ) :
    bloch v 0 0 = (v 2 : ℂ) ∧ bloch v 0 1 = (v 0 : ℂ) - (v 1 : ℂ) * Complex.I ∧
    bloch v 1 0 = (v 0 : ℂ) + (v 1 : ℂ) * Complex.I ∧ bloch v 1 1 = -(v 2 : ℂ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [bloch, sigmaX, sigmaY, sigmaZ] <;> ring

theorem bloch_herm (v : Fin 3 → ℝ) : (bloch v)ᴴ = bloch v := by
  obtain ⟨h00, h01, h10, h11⟩ := bloch_apply v
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, h00, h01, h10, h11, Complex.ext_iff]

theorem bloch_sq (v : Fin 3 → ℝ) (hv : ∑ i, v i ^ 2 = 1) : bloch v * bloch v = 1 := by
  obtain ⟨h00, h01, h10, h11⟩ := bloch_apply v
  have hv' : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by simpa [Fin.sum_univ_three] using hv
  have hvC : (v 0 : ℂ) ^ 2 + (v 1 : ℂ) ^ 2 + (v 2 : ℂ) ^ 2 = 1 := by exact_mod_cast hv'
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h10, h11] <;>
    first | ring1 | linear_combination hvC - (v 1 : ℂ) ^ 2 * Complex.I_sq

/-- conjugated Bloch matrix -/
def Mx (U : Mat 2) (v : Fin 3 → ℝ) : Mat 2 := Uᴴ * bloch v * U

theorem Mx_herm (U : Mat 2) (v : Fin 3 → ℝ) : (Mx U v)ᴴ = Mx U v := by
  simp [Mx, Matrix.conjTranspose_mul, bloch_herm, Matrix.mul_assoc]

theorem Mx_sq (U : Mat 2) (hU : IsUnitary U) (v : Fin 3 → ℝ) (hv : ∑ i, v i ^ 2 = 1) :
    Mx U v * Mx U v = 1 := by
  unfold Mx
  calc Uᴴ * bloch v * U * (Uᴴ * bloch v * U) = Uᴴ * bloch v * (U * Uᴴ) * bloch v * U := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU.2, Matrix.mul_one, Matrix.mul_assoc Uᴴ, bloch_sq v hv, Matrix.mul_one, hU.1]

theorem row_unit (M : Mat 2) (hM : Mᴴ = M) (h : M * M = 1) (i : Fin 2) :
    ‖M i 0‖ ^ 2 + ‖M i 1‖ ^ 2 = 1 := by
  have := congrFun (congrFun h i) i
  rw [Matrix.mul_apply, Fin.sum_univ_two] at this
  have hc : ∀ k, M k i = conj (M i k) := fun k => by
    have := congrFun (congrFun hM i) k
    rw [Matrix.conjTranspose_apply] at this
    rw [← this]; simp
  rw [hc 0, hc 1, Matrix.one_apply_eq] at this
  have e : ∀ z : ℂ, z * conj z = (‖z‖ ^ 2 : ℝ) := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e, e] at this
  exact_mod_cast this

/-- Bloch vector of the first column of U -/
def nv (U : Mat 2) : Fin 3 → ℝ :=
  ![2 * ((U 0 0).re * (U 1 0).re + (U 0 0).im * (U 1 0).im),
    2 * ((U 0 0).re * (U 1 0).im - (U 0 0).im * (U 1 0).re),
    (U 0 0).re * (U 0 0).re + (U 0 0).im * (U 0 0).im - (U 1 0).re * (U 1 0).re -
      (U 1 0).im * (U 1 0).im]

theorem Mx00 (U : Mat 2) (v : Fin 3 → ℝ) : Mx U v 0 0 = ((∑ i, v i * nv U i : ℝ) : ℂ) := by
  obtain ⟨h00, h01, h10, h11⟩ := bloch_apply v
  simp only [Mx, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, h00, h01, h10,
    h11, Fin.sum_univ_three, nv]
  apply Complex.ext <;> simp <;> ring

theorem nv_unit (U : Mat 2) (hU : IsUnitary U) : ∑ i, nv U i ^ 2 = 1 := by
  have := congrFun (congrFun hU.1 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_two] at this
  simp only [Matrix.conjTranspose_apply, Matrix.one_apply_eq] at this
  have h := congrArg Complex.re this
  simp at h
  simp only [Fin.sum_univ_three, nv]
  simp
  have : ((U 0 0).re ^ 2 + (U 0 0).im ^ 2 + (U 1 0).re ^ 2 + (U 1 0).im ^ 2) = 1 := by
    nlinarith [h]
  nlinarith [this]

/-! ### norm bounds for 2×2 matrices -/

theorem offdiag_le (X : Mat 2) (h00 : X 0 0 = 0) (h11 : X 1 1 = 0) (c : ℝ) (hc : 0 ≤ c)
    (h01 : ‖X 0 1‖ ≤ c) (h10 : ‖X 1 0‖ ≤ c) : SN X ≤ ENNReal.ofReal c := by
  unfold QAlgorithms.Papers.Independent.Information100.P47.spectralNorm
  refine iSup_le fun v => ENNReal.ofReal_le_ofReal ?_
  have hv := v.2
  have hsq : ‖QAlgorithms.act X v.val‖ ^ 2 =
      ‖X 0 1‖ ^ 2 * ‖v.val 1‖ ^ 2 + ‖X 1 0‖ ^ 2 * ‖v.val 0‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [QAlgorithms.act, Fin.sum_univ_two, PiLp.toLp_apply, Matrix.mulVec, dotProduct,
      h00, h11, zero_mul, zero_add, add_zero, norm_mul, mul_pow]
  have hv2 : ‖v.val 0‖ ^ 2 + ‖v.val 1‖ ^ 2 = 1 := by
    have := EuclideanSpace.norm_sq_eq v.val
    rw [hv, Fin.sum_univ_two] at this; linarith
  have a1 : ‖X 0 1‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h01 2
  have a2 : ‖X 1 0‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h10 2
  have : ‖QAlgorithms.act X v.val‖ ^ 2 ≤ c ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg ‖v.val 0‖, sq_nonneg ‖v.val 1‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc two_ne_zero).1 this

theorem col_le (X : Mat 2) (j : Fin 2) (t : ℝ) (ht : 0 ≤ t)
    (h : t ^ 2 ≤ ‖X 0 j‖ ^ 2 + ‖X 1 j‖ ^ 2) : ENNReal.ofReal t ≤ SN X := by
  unfold QAlgorithms.Papers.Independent.Information100.P47.spectralNorm
  set v : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single j 1
  have hv : ‖v‖ = 1 := by simp [v]
  refine le_trans ?_ (le_iSup _ ⟨v, hv⟩)
  apply ENNReal.ofReal_le_ofReal
  have hsq : ‖QAlgorithms.act X v‖ ^ 2 = ‖X 0 j‖ ^ 2 + ‖X 1 j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [QAlgorithms.act, v, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
  exact (pow_le_pow_iff_left₀ ht (norm_nonneg _) two_ne_zero).1 (hsq ▸ h)

theorem nsq_m (a b : ℝ) : ‖(a : ℂ) - (b : ℂ) * Complex.I‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

theorem nsq_p (a b : ℝ) : ‖(a : ℂ) + (b : ℂ) * Complex.I‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

/-! ### the SIC -/

section sic

variable (r : Fin 4 → Fin 3 → ℝ) (hr : IsTetrahedron r)
include hr

theorem sic_sum : ∑ x, sicPOVM r x = 1 := by
  have hs := sum_r r hr
  have h2 : ∑ x, bloch (r x) = 0 := by
    ext i j
    have e : ∀ x, bloch (r x) i j = ((r x 0 : ℂ) • sigmaX + (r x 1 : ℂ) • sigmaY +
        (r x 2 : ℂ) • sigmaZ) i j := fun x => rfl
    simp only [Matrix.sum_apply, e, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum, hs, Complex.ofReal_zero,
      zero_mul, add_zero, Matrix.zero_apply]
  simp only [sicPOVM, ← Finset.smul_sum, Finset.sum_add_distrib, h2, add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

theorem rot_eq (U : Mat 2) (hU : IsUnitary U) (x : Fin 4) :
    rotate U (sicPOVM r) x = (1/4 : ℂ) • (1 + Mx U (r x)) := by
  simp only [rotate, sicPOVM, Mx, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_one, hU.1]

theorem rot_sum (U : Mat 2) (hU : IsUnitary U) : ∑ x, rotate U (sicPOVM r) x = 1 := by
  simp only [rotate, ← Finset.sum_mul, ← Finset.mul_sum, sic_sum r hr, Matrix.mul_one, hU.1]

theorem diag_re (U : Mat 2) (hU : IsUnitary U) (x : Fin 4) (i : Fin 2) :
    (Mx U (r x) i i).im = 0 ∧ |(Mx U (r x) i i).re| ≤ 1 := by
  have hM := Mx_herm U (r x)
  have hsq := Mx_sq U hU (r x) (by simpa [sq] using gram r hr x x)
  have hrow := row_unit _ hM hsq i
  have him : (Mx U (r x) i i).im = 0 := by
    have := congrFun (congrFun hM i) i
    rw [Matrix.conjTranspose_apply] at this
    have h2 := congrArg Complex.im this
    simp at h2; linarith
  refine ⟨him, ?_⟩
  have hn : ‖Mx U (r x) i i‖ ≤ 1 := by
    have : ‖Mx U (r x) i i‖ ^ 2 ≤ 1 := by
      fin_cases i <;> simp at hrow ⊢ <;> nlinarith [sq_nonneg ‖Mx U (r x) 0 1‖,
        sq_nonneg ‖Mx U (r x) 1 0‖, sq_nonneg ‖Mx U (r x) 0 0‖, sq_nonneg ‖Mx U (r x) 1 1‖]
    nlinarith [norm_nonneg (Mx U (r x) i i)]
  exact (Complex.abs_re_le_norm _).trans hn

/-- the pinched (incoherent) POVM -/
def pinch (U : Mat 2) : Measurement 2 4 :=
  fun x => Matrix.diagonal fun i => rotate U (sicPOVM r) x i i

omit hr in
theorem pinch_incoh (U : Mat 2) : IsIncoherent (pinch r U) := by
  intro x i j hij
  simp [pinch, Matrix.diagonal_apply_ne _ hij]

theorem pinch_povm (U : Mat 2) (hU : IsUnitary U) :
    QAlgorithms.IsPOVM (pinch r U) := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [pinch, Matrix.posSemidef_diagonal_iff]
    intro i
    rw [rot_eq r hr U hU x]
    obtain ⟨him, hre⟩ := diag_re r hr U hU x i
    rw [Complex.nonneg_iff]
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply_eq, smul_eq_mul]
    constructor
    · simp; rw [abs_le] at hre; linarith
    · simp [him]
  · ext i j
    simp only [pinch, Matrix.sum_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp only [if_true]
      rw [← Matrix.sum_apply, rot_sum r hr U hU]
    · simp [hij, Matrix.one_apply_ne hij]

theorem coh_le (U : Mat 2) (hU : IsUnitary U) :
    coherence spectralDistance (rotate U (sicPOVM r)) ≤
      ENNReal.ofReal (Real.sqrt (32/3) / 8) := by
  refine le_trans (iInf_le _ ⟨pinch r U, pinch_povm r hr U hU, pinch_incoh r U⟩) ?_
  simp only [spectralDistance]
  set w : Fin 4 → ℝ := fun x => ‖Mx U (r x) 0 1‖
  have hX : ∀ x, SN (rotate U (sicPOVM r) x - pinch r U x) ≤ ENNReal.ofReal (w x / 4) := by
    intro x
    have hM := Mx_herm U (r x)
    have h10 : ‖Mx U (r x) 1 0‖ = w x := by
      have := congrFun (congrFun hM 1) 0
      rw [Matrix.conjTranspose_apply] at this
      rw [← this]; simp [w]
    apply offdiag_le _ (by simp [pinch]) (by simp [pinch]) _ (by positivity)
    · simp [pinch, rot_eq r hr U hU x, w]; exact le_of_eq (by ring)
    · simp [pinch, rot_eq r hr U hU x, h10]; exact le_of_eq (by ring)
  have hsum : ∑ x, SN (rotate U (sicPOVM r) x - pinch r U x) ≤
      ENNReal.ofReal (∑ x, w x / 4) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => by positivity)]
    exact Finset.sum_le_sum fun x _ => hX x
  -- bound on Σ w
  have hw2 : ∑ x, w x ^ 2 = 8/3 := by
    have hz : ∀ x, w x ^ 2 = 1 - (∑ i, r x i * nv U i) ^ 2 := by
      intro x
      have hrow := row_unit _ (Mx_herm U (r x)) (Mx_sq U hU (r x)
        (by simpa [sq] using gram r hr x x)) 0
      rw [Mx00, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hrow
      simp only [w]; linarith
    simp only [hz, Finset.sum_sub_distrib, tight r hr, nv_unit U hU]
    simp; norm_num
  have hcs : (∑ x, w x) ^ 2 ≤ 32/3 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := w)
    rw [hw2] at this; simp at this; linarith
  have hw : ∑ x, w x ≤ Real.sqrt (32/3) :=
    Real.le_sqrt_of_sq_le hcs
  calc (1/2 : ℝ≥0∞) * ∑ x, SN (rotate U (sicPOVM r) x - pinch r U x)
      ≤ (1/2 : ℝ≥0∞) * ENNReal.ofReal (∑ x, w x / 4) := by gcongr
    _ = ENNReal.ofReal ((1/2) * ∑ x, w x / 4) := by
        rw [ENNReal.ofReal_mul (by norm_num)]; congr 1; simp
    _ ≤ ENNReal.ofReal (Real.sqrt (32/3) / 8) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Finset.sum_div]; linarith

theorem sharp_ge : (1/2 : ℝ≥0∞) ≤ sharpness spectralDistance (sicPOVM r) := by
  refine le_iInf fun p => ?_
  simp only [spectralDistance]
  have h : ∀ x, ENNReal.ofReal (1/4) ≤ SN (sicPOVM r x - QAlgorithms.Papers.Independent.Information100.P47.trivial p.val x) := by
    intro x
    set X := sicPOVM r x - QAlgorithms.Papers.Independent.Information100.P47.trivial p.val x
    have hv := gram r hr x x
    simp only [Fin.sum_univ_three] at hv
    obtain ⟨h00, h01, h10, h11⟩ := bloch_apply (r x)
    have e00 : X 0 0 = ((1/4 - p.val x + r x 2 / 4 : ℝ) : ℂ) := by
      simp [X, sicPOVM, QAlgorithms.Papers.Independent.Information100.P47.trivial, h00]; ring
    have e11 : X 1 1 = ((1/4 - p.val x - r x 2 / 4 : ℝ) : ℂ) := by
      simp [X, sicPOVM, QAlgorithms.Papers.Independent.Information100.P47.trivial, h11]; ring
    have e01 : ‖X 0 1‖ ^ 2 = (r x 0 ^ 2 + r x 1 ^ 2) / 16 := by
      have : X 0 1 = (1/4 : ℂ) * ((r x 0 : ℂ) - (r x 1 : ℂ) * Complex.I) := by
        simp [X, sicPOVM, QAlgorithms.Papers.Independent.Information100.P47.trivial, h01]
      rw [this, norm_mul, mul_pow, nsq_m]; norm_num; ring
    have e10 : ‖X 1 0‖ ^ 2 = (r x 0 ^ 2 + r x 1 ^ 2) / 16 := by
      have : X 1 0 = (1/4 : ℂ) * ((r x 0 : ℂ) + (r x 1 : ℂ) * Complex.I) := by
        simp [X, sicPOVM, QAlgorithms.Papers.Independent.Information100.P47.trivial, h10]
      rw [this, norm_mul, mul_pow, nsq_p]; norm_num; ring
    have n00 : ‖X 0 0‖ ^ 2 = (1/4 - p.val x + r x 2 / 4) ^ 2 := by
      rw [e00, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have n11 : ‖X 1 1‖ ^ 2 = (1/4 - p.val x - r x 2 / 4) ^ 2 := by
      rw [e11, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    by_cases hc : (1/4 : ℝ) ^ 2 ≤ ‖X 0 0‖ ^ 2 + ‖X 1 0‖ ^ 2
    · exact col_le X 0 _ (by norm_num) hc
    · apply col_le X 1 _ (by norm_num)
      push Not at hc
      rw [n00, e10] at hc
      rw [e01, n11]
      simp only [if_true] at hv
      nlinarith [sq_nonneg (1/4 - p.val x), sq_nonneg (r x 2)]
  calc (1/2 : ℝ≥0∞) = (1/2) * ∑ _x : Fin 4, ENNReal.ofReal (1/4) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
        norm_num
    _ ≤ _ := by gcongr with x; exact h x

theorem gap : maxCoherence spectralDistance (sicPOVM r) < sharpness spectralDistance (sicPOVM r) := by
  refine lt_of_le_of_lt (iSup_le fun U => coh_le r hr U.val U.2) (lt_of_lt_of_le ?_ (sharp_ge r hr))
  have : Real.sqrt (32/3) / 8 < 1/2 := by
    have : Real.sqrt (32/3) < 4 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  calc ENNReal.ofReal (Real.sqrt (32/3) / 8) < ENNReal.ofReal (1/2) :=
        (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 this
    _ = 1/2 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp

end sic

end X6P47S

open QAlgorithms.Papers.Independent.Information100.P47 in
theorem solution (r : Fin 4 → Fin 3 → ℝ) (hr : IsTetrahedron r) :
    maxCoherence spectralDistance (sicPOVM r) < sharpness spectralDistance (sicPOVM r) :=
  X6P47S.gap r hr
