-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.relative_entropy_axioms
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:22:51.48637+00:00
-- url     : https://prove2.me/submissions/86ed9a8e-5902-40d9-bc17-47dc329ac16a

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
import Mathlib
import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_alphaOneLimit
import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_alphaMonotone
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_backgroundSSA
import Theorems.Thm_QAlgorithms_Arunachalam_vnEntropy_subadditive
import Theorems.Thm_SimpleSSA_Monotone_eq_4
import Theorems.Thm_BanditAlgorithm_bernoulli_relative_entropy_pinsker
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model

section X5mod_OL_Base
open Matrix
open scoped ComplexOrder

namespace X5OL

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- overlap matrix of the two eigenbases -/
noncomputable def ov {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) : Matrix I I ℂ :=
  star (hR.eigenvectorUnitary : Matrix I I ℂ) * (hN.eigenvectorUnitary : Matrix I I ℂ)

noncomputable def w {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) : ℝ :=
  ‖ov hR hN i j‖ ^ 2

lemma ov_unitary {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) :
    ov hR hN * star (ov hR hN) = 1 := by
  unfold ov
  have hU : star (hR.eigenvectorUnitary : Matrix I I ℂ) * (hR.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Unitary.star_mul_self_of_mem (hR.eigenvectorUnitary).2
  have hV : (hN.eigenvectorUnitary : Matrix I I ℂ) * star (hN.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Unitary.mul_star_self_of_mem (hN.eigenvectorUnitary).2
  rw [star_mul, star_star, Matrix.mul_assoc, ← Matrix.mul_assoc (hN.eigenvectorUnitary : Matrix I I ℂ),
    hV, Matrix.one_mul, hU]

lemma w_row {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i : I) :
    ∑ j, w hR hN i j = 1 := by
  have h := congrFun (congrFun (ov_unitary hR hN) i) i
  rw [mul_apply, one_apply_eq] at h
  have : (∑ j, ((w hR hN i j : ℝ) : ℂ)) = 1 := by
    rw [← h]; refine Finset.sum_congr rfl fun j _ => ?_
    simp only [w, star_apply, Complex.ofReal_pow]
    rw [RCLike.star_def, Complex.mul_conj']
  exact_mod_cast this

lemma w_nonneg {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) :
    0 ≤ w hR hN i j := by unfold w; positivity

lemma tr_cfc_cfc {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (f g : ℝ → ℝ) :
    (cfc f R * cfc g N).trace =
      ∑ i, ∑ j, ((f (hR.eigenvalues i) * g (hN.eigenvalues j) * w hR hN i j : ℝ) : ℂ) := by
  rw [hR.cfc_eq, hN.cfc_eq]
  unfold IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply]
  set U := (hR.eigenvectorUnitary : Matrix I I ℂ)
  set V := (hN.eigenvectorUnitary : Matrix I I ℂ)
  set Df := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ f ∘ hR.eigenvalues)
  set Dg := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ g ∘ hN.eigenvalues)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (hR.eigenvectorUnitary).2
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem (hR.eigenvectorUnitary).2
  have : (U * Df * star U * (V * Dg * star V)).trace = (Df * (star U * V) * Dg * star (star U * V)).trace := by
    rw [star_mul, star_star]
    rw [show U * Df * star U * (V * Dg * star V) = U * (Df * (star U * V) * Dg * (star V * U)) * star U by
      simp only [Matrix.mul_assoc]; rw [hU']; simp]
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  rw [this]
  change (Df * ov hR hN * Dg * star (ov hR hN)).trace = _
  have hE : ∀ i k, (Df * ov hR hN * Dg) i k =
      ((f (hR.eigenvalues i) : ℝ) : ℂ) * ov hR hN i k * ((g (hN.eigenvalues k) : ℝ) : ℂ) := by
    intro i k; simp [Df, Dg, diagonal_mul, mul_diagonal]
  simp only [Matrix.trace, diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hE, star_apply]
  simp only [w, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [← Complex.mul_conj', RCLike.star_def]
  ring

lemma ov_apply {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) :
    ov hR hN i j = star (hR.eigenvectorBasis i).ofLp ⬝ᵥ (hN.eigenvectorBasis j).ofLp := by
  simp only [ov, mul_apply, star_apply, IsHermitian.eigenvectorUnitary_apply, dotProduct, Pi.star_apply]

lemma supp_fwd {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian)
    (h : LinearMap.ker N.mulVecLin ≤ LinearMap.ker R.mulVecLin) (i j : I)
    (hi : hR.eigenvalues i ≠ 0) (hj : hN.eigenvalues j = 0) : ov hR hN i j = 0 := by
  set b := (hR.eigenvectorBasis i).ofLp
  set v := (hN.eigenvectorBasis j).ofLp
  have hNv : N *ᵥ v = 0 := by rw [hN.mulVec_eigenvectorBasis j, hj, zero_smul]
  have hRv : R *ᵥ v = 0 := by
    have := h (show v ∈ LinearMap.ker N.mulVecLin by rw [LinearMap.mem_ker, mulVecLin_apply]; exact hNv)
    rwa [LinearMap.mem_ker, mulVecLin_apply] at this
  have key : ((hR.eigenvalues i : ℝ) : ℂ) * (star b ⬝ᵥ v) = 0 := by
    have hb : R *ᵥ b = hR.eigenvalues i • b := hR.mulVec_eigenvectorBasis i
    have : star (R *ᵥ b) ⬝ᵥ v = star b ⬝ᵥ (R *ᵥ v) := by
      rw [star_mulVec, hR.eq, dotProduct_mulVec]
    rw [hRv, dotProduct_zero, hb, star_smul] at this
    rw [← this, smul_dotProduct]
    simp [RCLike.real_smul_eq_coe_mul]
  rw [ov_apply]
  rcases mul_eq_zero.1 key with h1 | h1
  · exact absurd (by exact_mod_cast h1) hi
  · exact h1

end X5OL
end X5mod_OL_Base

section X5mod_PQ_Key
open Matrix
open scoped ComplexOrder

namespace X5PQ

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma scal (z Y : ℂ) {c : ℝ} (hc : 0 < c) : 2 * (star z * Y).re - c * ‖Y‖ ^ 2 ≤ ‖z‖ ^ 2 / c := by
  rw [le_div_iff₀ hc]
  have h1 : ‖Y‖ ^ 2 = Y.re ^ 2 + Y.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h3 : (star z * Y).re = z.re * Y.re + z.im * Y.im := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [h1, h2, h3]
  nlinarith [sq_nonneg (z.re - c * Y.re), sq_nonneg (z.im - c * Y.im)]

lemma scal' (z Y : ℂ) {c : ℝ} (hc : 0 ≤ c) (hz : c = 0 → z = 0) :
    2 * (star z * Y).re - c * ‖Y‖ ^ 2 ≤ ‖z‖ ^ 2 / c := by
  rcases hc.lt_or_eq with hc | hc
  · exact scal z Y hc
  · subst hc; simp [hz rfl]

lemma row_sum (M : Matrix I I ℂ) (a : I) :
    (M * Mᴴ) a a = ((∑ b, ‖M a b‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]; push_cast
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [conjTranspose_apply, ← Complex.mul_conj', RCLike.star_def]

lemma col_sum (M : Matrix I I ℂ) (b : I) :
    (Mᴴ * M) b b = ((∑ a, ‖M a b‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]; push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [conjTranspose_apply, ← Complex.conj_mul', RCLike.star_def]

end X5PQ
end X5mod_PQ_Key

section X5mod_DP_Var
open Matrix
open scoped ComplexOrder

namespace X5DP

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def G (A B : ℝ) {X Y : Matrix I I ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) : ℝ :=
  ∑ a, ∑ b, X5OL.w hX hY a b * hX.eigenvalues a ^ 2 / (A * hX.eigenvalues a + B * hY.eigenvalues b)

noncomputable def val (A B : ℝ) (X Y Z : Matrix I I ℂ) : ℝ :=
  2 * (Zᴴ * X).trace.re - A * (Zᴴ * X * Z).trace.re - B * (Z * Y * Zᴴ).trace.re

lemma spec_eq {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix I I ℂ) * diagonal (fun a => ((hX.eigenvalues a : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix I I ℂ)ᴴ := by
  conv_lhs => rw [hX.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]; rfl

lemma tr_spec (M : Matrix I I ℂ) {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    (M * X).trace = ∑ a, ((hX.eigenvectorUnitary : Matrix I I ℂ)ᴴ * M *
      (hX.eigenvectorUnitary : Matrix I I ℂ)) a a * ((hX.eigenvalues a : ℝ) : ℂ) := by
  set E := (hX.eigenvectorUnitary : Matrix I I ℂ)
  conv_lhs => rw [spec_eq hX]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]
  simp only [Matrix.trace, diag_apply, mul_diagonal]
  rfl

lemma EE {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    (hX.eigenvectorUnitary : Matrix I I ℂ) * (hX.eigenvectorUnitary : Matrix I I ℂ)ᴴ = 1 := by
  rw [← star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2

lemma EE' {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    (hX.eigenvectorUnitary : Matrix I I ℂ)ᴴ * (hX.eigenvectorUnitary : Matrix I I ℂ) = 1 := by
  rw [← star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2

/-- `val` in the joint eigen-coordinates `Z' = Eᴴ Z F`. -/
lemma val_coord (A B : ℝ) {X Y : Matrix I I ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (Z : Matrix I I ℂ) :
    val A B X Y Z = ∑ a, ∑ b, (2 * hX.eigenvalues a *
      (star (X5OL.ov hX hY a b) * ((hX.eigenvectorUnitary : Matrix I I ℂ)ᴴ * Z *
        (hY.eigenvectorUnitary : Matrix I I ℂ)) a b).re -
      (A * hX.eigenvalues a + B * hY.eigenvalues b) *
        ‖((hX.eigenvectorUnitary : Matrix I I ℂ)ᴴ * Z * (hY.eigenvectorUnitary : Matrix I I ℂ)) a b‖ ^ 2) := by
  set E := (hX.eigenvectorUnitary : Matrix I I ℂ)
  set F := (hY.eigenvectorUnitary : Matrix I I ℂ)
  set Z' := Eᴴ * Z * F
  set o := X5OL.ov hX hY
  have ho : o = Eᴴ * F := by simp [o, X5OL.ov, E, F, star_eq_conjTranspose]
  -- three identities
  have i1 : Eᴴ * Zᴴ * E = (Z' * oᴴ)ᴴ := by
    rw [ho]; simp only [Z', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F, EE hY, Matrix.one_mul]
  have i2 : Eᴴ * (Z * Zᴴ) * E = Z' * Z'ᴴ := by
    simp only [Z', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F, EE hY, Matrix.one_mul]
  have i3 : Fᴴ * (Zᴴ * Z) * F = Z'ᴴ * Z' := by
    simp only [Z', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc E (Eᴴ), EE hX, Matrix.one_mul]
  have t1 : (Zᴴ * X).trace.re = ∑ a, ∑ b, hX.eigenvalues a * (star (o a b) * Z' a b).re := by
    rw [tr_spec _ hX, i1, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [conjTranspose_apply, mul_comm, Complex.re_ofReal_mul, Complex.star_def, Complex.conj_re,
      Matrix.mul_apply, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [conjTranspose_apply, mul_comm (Z' a b)]; rfl
  have t2 : (Zᴴ * X * Z).trace.re = ∑ a, ∑ b, hX.eigenvalues a * ‖Z' a b‖ ^ 2 := by
    rw [Matrix.trace_mul_cycle, tr_spec _ hX, i2, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [X5PQ.row_sum, ← Complex.ofReal_mul, Complex.ofReal_re, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  have t3 : (Z * Y * Zᴴ).trace.re = ∑ a, ∑ b, hY.eigenvalues b * ‖Z' a b‖ ^ 2 := by
    rw [Matrix.trace_mul_cycle, tr_spec _ hY, i3, Complex.re_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [X5PQ.col_sum, ← Complex.ofReal_mul, Complex.ofReal_re, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  unfold val
  rw [t1, t2, t3]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma var_le (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) {X Y : Matrix I I ℂ} (hX : X.PosSemidef)
    (hY : Y.PosSemidef)
    (hs : ∀ a b, A * hX.isHermitian.eigenvalues a + B * hY.isHermitian.eigenvalues b = 0 →
      (hX.isHermitian.eigenvalues a : ℂ) * X5OL.ov hX.isHermitian hY.isHermitian a b = 0)
    (Z : Matrix I I ℂ) : val A B X Y Z ≤ G A B hX.isHermitian hY.isHermitian := by
  rw [val_coord A B hX.isHermitian hY.isHermitian]
  unfold G
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  set l := hX.isHermitian.eigenvalues a
  set m := hY.isHermitian.eigenvalues b
  set o := X5OL.ov hX.isHermitian hY.isHermitian a b
  set y := ((hX.isHermitian.eigenvectorUnitary : Matrix I I ℂ)ᴴ * Z *
    (hY.isHermitian.eigenvectorUnitary : Matrix I I ℂ)) a b
  have hl : 0 ≤ l := hX.eigenvalues_nonneg a
  have hm : 0 ≤ m := hY.eigenvalues_nonneg b
  have := X5PQ.scal' ((l : ℂ) * o) y (c := A * l + B * m)
    (add_nonneg (mul_nonneg hA hl) (mul_nonneg hB hm)) (hs a b)
  have e1 : (star ((l : ℂ) * o) * y).re = l * (star o * y).re := by
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
  have e2 : ‖(l : ℂ) * o‖ ^ 2 = X5OL.w hX.isHermitian hY.isHermitian a b * l ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl, X5OL.w]; ring
  rw [e1, e2] at this; linarith

lemma var_eq (A B : ℝ) {X Y : Matrix I I ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    ∃ Z, val A B X Y Z = G A B hX hY := by
  set E := (hX.eigenvectorUnitary : Matrix I I ℂ)
  set F := (hY.eigenvectorUnitary : Matrix I I ℂ)
  set o := X5OL.ov hX hY
  set Z' : Matrix I I ℂ := Matrix.of fun a b => ((hX.eigenvalues a : ℝ) : ℂ) * o a b /
    ((A * hX.eigenvalues a + B * hY.eigenvalues b : ℝ) : ℂ)
  refine ⟨E * Z' * Fᴴ, ?_⟩
  rw [val_coord A B hX hY]
  have hZ : Eᴴ * (E * Z' * Fᴴ) * F = Z' := by
    simp only [Matrix.mul_assoc]; rw [EE' hY, Matrix.mul_one, ← Matrix.mul_assoc, EE' hX, Matrix.one_mul]
  rw [hZ]
  unfold G
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  set l := hX.eigenvalues a
  set c := A * hX.eigenvalues a + B * hY.eigenvalues b
  have hw : X5OL.w hX hY a b = ‖o a b‖ ^ 2 := rfl
  simp only [Z', Matrix.of_apply]
  rw [hw]
  by_cases hc : c = 0
  · simp [c, hc] at *
  · have e1 : (star (o a b) * ((l : ℂ) * o a b / (c : ℂ))).re = l * ‖o a b‖ ^ 2 / c := by
      rw [show star (o a b) * ((l : ℂ) * o a b / (c : ℂ)) = (((l / c * ‖o a b‖ ^ 2 : ℝ)) : ℂ) by
        have h0 : star (o a b) * o a b = ((‖o a b‖ ^ 2 : ℝ) : ℂ) := by
          rw [RCLike.star_def, Complex.conj_mul']; push_cast; rfl
        calc star (o a b) * ((l : ℂ) * o a b / (c : ℂ)) = (l : ℂ) / c * (star (o a b) * o a b) := by ring
          _ = _ := by rw [h0]; push_cast; ring]
      rw [Complex.ofReal_re]; ring
    have e2 : ‖(l : ℂ) * o a b / (c : ℂ)‖ ^ 2 = l ^ 2 * ‖o a b‖ ^ 2 / c ^ 2 := by
      rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, div_pow, mul_pow, Real.norm_eq_abs,
        Real.norm_eq_abs, sq_abs, sq_abs]
    rw [e1, e2]
    field_simp
    ring

end X5DP
end X5mod_DP_Var

section X5mod_DP_KS
open Matrix
open scoped ComplexOrder

namespace X5DP

variable {ι κ J : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype J]

def Φ (K : J → Matrix κ ι ℂ) (X : Matrix ι ι ℂ) : Matrix κ κ ℂ := ∑ j, K j * X * (K j)ᴴ
def Φd (K : J → Matrix κ ι ℂ) (Q : Matrix κ κ ℂ) : Matrix ι ι ℂ := ∑ j, (K j)ᴴ * Q * K j

lemma tr_nonneg' {r s : Type*} [Fintype r] [Fintype s] (M : Matrix r s ℂ) : 0 ≤ (Mᴴ * M).trace.re := by
  simp only [Matrix.trace, diag_apply, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => ?_
  rw [RCLike.star_def, Complex.conj_mul']
  norm_cast
  positivity

lemma cs {r : Type*} [Fintype r] (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1)
    (M : J → Matrix κ r ℂ) :
    ((∑ j, (K j)ᴴ * M j)ᴴ * (∑ j, (K j)ᴴ * M j)).trace.re ≤ ∑ j, ((M j)ᴴ * M j).trace.re := by
  set V := ∑ j, (K j)ᴴ * M j
  have hV : ∑ j, (M j)ᴴ * K j = Vᴴ := by
    simp only [V, conjTranspose_sum, conjTranspose_mul, conjTranspose_conjTranspose]
  have h0 : 0 ≤ ∑ j, ((M j - K j * V)ᴴ * (M j - K j * V)).trace.re :=
    Finset.sum_nonneg fun j _ => tr_nonneg' _
  have hexp : ∑ j, (M j - K j * V)ᴴ * (M j - K j * V) =
      ∑ j, (M j)ᴴ * M j - Vᴴ * V := by
    have e : ∀ j, (M j - K j * V)ᴴ * (M j - K j * V) =
        (M j)ᴴ * M j - ((M j)ᴴ * K j) * V - Vᴴ * ((K j)ᴴ * M j) + Vᴴ * ((K j)ᴴ * K j) * V := by
      intro j
      simp only [conjTranspose_sub, conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    have s1 : ∑ j, ((M j)ᴴ * K j) * V = Vᴴ * V := by rw [← Matrix.sum_mul, hV]
    have s2 : ∑ j, Vᴴ * ((K j)ᴴ * M j) = Vᴴ * V := by rw [← Matrix.mul_sum]
    have s3 : ∑ j, Vᴴ * ((K j)ᴴ * K j) * V = Vᴴ * V := by
      rw [← Matrix.sum_mul, ← Matrix.mul_sum, hK, Matrix.mul_one]
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, s1, s2, s3]
    abel
  have := congrArg (fun T => (Matrix.trace T).re) hexp
  simp only [Matrix.trace_sum, Matrix.trace_sub, Complex.re_sum, Complex.sub_re] at this
  rw [this] at h0
  linarith

omit [DecidableEq κ] in
lemma exists_sq {X : Matrix ι ι ℂ} (hX : X.PosSemidef) : ∃ B : Matrix ι ι ℂ, X = Bᴴ * B := by
  refine ⟨diagonal (fun a => ((Real.sqrt (hX.isHermitian.eigenvalues a) : ℝ) : ℂ)) *
    (hX.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ, ?_⟩
  rw [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
  conv_lhs => rw [spec_eq hX.isHermitian]
  rw [show ∀ (P D1 D2 : Matrix ι ι ℂ), P * D1 * (D2 * Pᴴ) = P * (D1 * D2) * Pᴴ from
    fun P D1 D2 => by simp only [Matrix.mul_assoc], diagonal_mul_diagonal]
  congr 3
  ext a
  simp only [Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hX.eigenvalues_nonneg a)]

/-- Kadison–Schwarz in trace form. -/
lemma ks_tr (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) {X : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (Z : Matrix κ κ ℂ) :
    (X * (Φd K Z * (Φd K Z)ᴴ)).trace.re ≤ (X * Φd K (Z * Zᴴ)).trace.re := by
  obtain ⟨B, rfl⟩ := exists_sq hX
  have h := cs K hK (fun j => Zᴴ * K j * Bᴴ)
  have e1 : ∑ j, (K j)ᴴ * (Zᴴ * K j * Bᴴ) = (Φd K Z)ᴴ * Bᴴ := by
    simp only [Φd, conjTranspose_sum, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.sum_mul,
      Matrix.mul_assoc]
  rw [e1] at h
  set W := Φd K Z
  have e2 : ((Wᴴ * Bᴴ)ᴴ * (Wᴴ * Bᴴ)).trace = (Bᴴ * B * (W * Wᴴ)).trace := by
    calc ((Wᴴ * Bᴴ)ᴴ * (Wᴴ * Bᴴ)).trace = ((B * W * Wᴴ) * Bᴴ).trace := by
          rw [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_conjTranspose]
          simp only [Matrix.mul_assoc]
      _ = (Bᴴ * (B * W * Wᴴ)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  have e3 : ∑ j, ((Zᴴ * K j * Bᴴ)ᴴ * (Zᴴ * K j * Bᴴ)).trace.re = (Bᴴ * B * Φd K (Z * Zᴴ)).trace.re := by
    simp only [Φd, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    calc ((Zᴴ * K j * Bᴴ)ᴴ * (Zᴴ * K j * Bᴴ)).trace = ((B * (K j)ᴴ * Z * Zᴴ * K j) * Bᴴ).trace := by
          rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
            conjTranspose_conjTranspose]
          simp only [Matrix.mul_assoc]
      _ = (Bᴴ * (B * (K j)ᴴ * Z * Zᴴ * K j)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e2, e3] at h
  exact h

lemma tr_dual (K : J → Matrix κ ι ℂ) (Q : Matrix κ κ ℂ) (X : Matrix ι ι ℂ) :
    (Q * Φ K X).trace = (Φd K Q * X).trace := by
  simp only [Φ, Φd, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Q * (K j * X * (K j)ᴴ) = (Q * (K j * X)) * (K j)ᴴ by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

lemma Φd_star (K : J → Matrix κ ι ℂ) (Z : Matrix κ κ ℂ) : Φd K Zᴴ = (Φd K Z)ᴴ := by
  simp only [Φd, conjTranspose_sum, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma val_mono (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) (Z : Matrix κ κ ℂ) :
    val A B (Φ K X) (Φ K Y) Z ≤ val A B X Y (Φd K Z) := by
  unfold val
  have t1 : (Zᴴ * Φ K X).trace = ((Φd K Z)ᴴ * X).trace := by rw [tr_dual, Φd_star]
  have t2 : (Zᴴ * Φ K X * Z).trace = (X * Φd K (Z * Zᴴ)).trace := by
    rw [Matrix.trace_mul_cycle, tr_dual, Matrix.trace_mul_comm]
  have t2' : ((Φd K Z)ᴴ * X * Φd K Z).trace = (X * (Φd K Z * (Φd K Z)ᴴ)).trace := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  have t3 : (Z * Φ K Y * Zᴴ).trace = (Y * Φd K (Zᴴ * Z)).trace := by
    rw [Matrix.trace_mul_cycle, tr_dual, Matrix.trace_mul_comm]
  have t3' : (Φd K Z * Y * (Φd K Z)ᴴ).trace = (Y * (Φd K Zᴴ * (Φd K Zᴴ)ᴴ)).trace := by
    rw [Φd_star, conjTranspose_conjTranspose, Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  have k2 := ks_tr K hK hX Z
  have k3 := ks_tr K hK hY Zᴴ
  rw [conjTranspose_conjTranspose] at k3
  rw [t1, t2, t2', t3, t3']
  nlinarith [mul_le_mul_of_nonneg_left k2 hA, mul_le_mul_of_nonneg_left k3 hB]

theorem G_mono (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hX' : (Φ K X).PosSemidef) (hY' : (Φ K Y).PosSemidef)
    (hs : ∀ a b, A * hX.isHermitian.eigenvalues a + B * hY.isHermitian.eigenvalues b = 0 →
      (hX.isHermitian.eigenvalues a : ℂ) * X5OL.ov hX.isHermitian hY.isHermitian a b = 0) :
    G A B hX'.isHermitian hY'.isHermitian ≤ G A B hX.isHermitian hY.isHermitian := by
  obtain ⟨Z, hZ⟩ := var_eq A B hX'.isHermitian hY'.isHermitian
  rw [← hZ]
  exact (val_mono K hK A B hA hB hX hY Z).trans (var_le A B hA hB hX hY hs _)

end X5DP
end X5mod_DP_KS

section X5mod_PQ_Int
open MeasureTheory Set Real

namespace X5PQ

noncomputable def K (p : ℝ) : ℝ := ∫ t in Ioi 0, rpowIntegrand₀₁ (p - 1) t 1

lemma K_pos {p : ℝ} (hp : p ∈ Ioo 1 2) : 0 < K p :=
  integral_rpowIntegrand₀₁_one_pos ⟨by linarith [hp.1], by linarith [hp.2]⟩

noncomputable def φ (p t x y : ℝ) : ℝ := t ^ (p - 2) * (x ^ 2 / (x + t * y))

lemma phi_eq {p t x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (ht : 0 < t) :
    y * rpowIntegrand₁₂ p t (x / y) = φ p t x y := by
  unfold rpowIntegrand₁₂ φ
  have e : t ^ (p - 1) = t ^ (p - 2) * t := by
    rw [show p - 1 = (p - 2) + 1 by ring, rpow_add ht, rpow_one]
  rw [e]
  have h1 : 0 < x + t * y := by positivity
  have h2 : t + x / y ≠ 0 := by positivity
  have h3 : t + x / y = (x + t * y) / y := by field_simp; ring
  rw [h3]
  field_simp
  ring

lemma phi_int {p x y : ℝ} (hp : p ∈ Ioo 1 2) (hx : 0 ≤ x) (hy : 0 < y) :
    IntegrableOn (fun t => φ p t x y) (Ioi 0) := by
  have : IntegrableOn (fun t => y * rpowIntegrand₁₂ p t (x / y)) (Ioi 0) :=
    (integrableOn_rpowIntegrand₁₂ hp (div_nonneg hx hy.le)).const_mul y
  exact IntegrableOn.congr_fun this (fun t ht => phi_eq hx hy ht) measurableSet_Ioi

lemma persp {p x y : ℝ} (hp : p ∈ Ioo 1 2) (hx : 0 ≤ x) (hy : 0 < y) :
    x ^ p * y ^ (1 - p) = (K p)⁻¹ * ∫ t in Ioi 0, φ p t x y := by
  have e1 : x ^ p * y ^ (1 - p) = y * (x / y) ^ p := by
    rw [div_rpow hx hy.le, rpow_sub hy, rpow_one]; field_simp
  rw [e1, rpow_eq_const_mul_integral_rpowIntegrand₁₂ hp (div_nonneg hx hy.le)]
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun t ht => phi_eq (p := p) hx hy ht),
    integral_const_mul]
  unfold K; ring

end X5PQ
end X5mod_PQ_Int

section X5mod_DP_Int
open MeasureTheory Set Real

namespace X5DP

/-- generic comparison of finite sums of integral representations -/
theorem cmp_gen {ι κ : Type*} (S : Finset ι) (T : Finset κ) (x y c : ι → ℝ) (u v d : κ → ℝ)
    (F : ℝ → ℝ → ℝ) (φ : ℝ → ℝ → ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hrep : ∀ x y : ℝ, 0 ≤ x → 0 < y → F x y = C * ∫ s in Ioi 0, φ s x y)
    (hint : ∀ x y : ℝ, 0 ≤ x → 0 < y → IntegrableOn (fun s => φ s x y) (Ioi 0))
    (hx : ∀ i ∈ S, 0 ≤ x i) (hy : ∀ i ∈ S, 0 < y i) (hu : ∀ k ∈ T, 0 ≤ u k) (hv : ∀ k ∈ T, 0 < v k)
    (h : ∀ s, 0 < s → ∑ i ∈ S, c i * φ s (x i) (y i) ≤ ∑ k ∈ T, d k * φ s (u k) (v k)) :
    ∑ i ∈ S, c i * F (x i) (y i) ≤ ∑ k ∈ T, d k * F (u k) (v k) := by
  have hL : ∑ i ∈ S, c i * F (x i) (y i) = C * ∫ s in Ioi 0, ∑ i ∈ S, c i * φ s (x i) (y i) := by
    rw [integral_finsetSum S fun i hi => (hint _ _ (hx i hi) (hy i hi)).const_mul (c i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hrep _ _ (hx i hi) (hy i hi), integral_const_mul]; ring
  have hR : ∑ k ∈ T, d k * F (u k) (v k) = C * ∫ s in Ioi 0, ∑ k ∈ T, d k * φ s (u k) (v k) := by
    rw [integral_finsetSum T fun k hk => (hint _ _ (hu k hk) (hv k hk)).const_mul (d k), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hrep _ _ (hu k hk) (hv k hk), integral_const_mul]; ring
  rw [hL, hR]
  refine mul_le_mul_of_nonneg_left ?_ hC
  exact setIntegral_mono_on
    (integrable_finsetSum S fun i hi => (hint _ _ (hx i hi) (hy i hi)).const_mul (c i))
    (integrable_finsetSum T fun k hk => (hint _ _ (hu k hk) (hv k hk)).const_mul (d k))
    measurableSet_Ioi h

/-- integrand for `p ∈ (0,1)` -/
noncomputable def φ0 (p s x y : ℝ) : ℝ := s ^ (p - 1) * y - s ^ p * (y ^ 2 / (x + s * y))

lemma phi0_eq {p s x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hs : 0 < s) :
    y * rpowIntegrand₀₁ p s (x / y) = φ0 p s x y := by
  unfold rpowIntegrand₀₁ φ0
  have e : s ^ (p - 1) = s ^ p * s⁻¹ := by rw [rpow_sub_one hs.ne', div_eq_mul_inv]
  rw [e]
  have h1 : 0 < x + s * y := by positivity
  have h3 : s + x / y = (x + s * y) / y := by field_simp; ring
  rw [h3]
  field_simp

lemma phi0_int {p x y : ℝ} (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) (hy : 0 < y) :
    IntegrableOn (fun s => φ0 p s x y) (Ioi 0) := by
  have : IntegrableOn (fun s => y * rpowIntegrand₀₁ p s (x / y)) (Ioi 0) :=
    (integrableOn_rpowIntegrand₀₁_Ioi hp (div_nonneg hx hy.le)).const_mul y
  exact IntegrableOn.congr_fun this (fun s hs => phi0_eq hx hy hs) measurableSet_Ioi

lemma persp0 {p x y : ℝ} (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) (hy : 0 < y) :
    x ^ p * y ^ (1 - p) = (∫ s in Ioi 0, rpowIntegrand₀₁ p s 1)⁻¹ * ∫ s in Ioi 0, φ0 p s x y := by
  have e1 : x ^ p * y ^ (1 - p) = y * (x / y) ^ p := by
    rw [div_rpow hx hy.le, rpow_sub hy, rpow_one]; field_simp
  rw [e1, rpow_eq_const_mul_integral hp (div_nonneg hx hy.le)]
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun s hs => phi0_eq (p := p) hx hy hs),
    integral_const_mul]
  ring

lemma K0_pos {p : ℝ} (hp : p ∈ Ioo 0 1) : 0 < ∫ s in Ioi 0, rpowIntegrand₀₁ p s 1 :=
  integral_rpowIntegrand₀₁_one_pos hp

end X5DP
end X5mod_DP_Int

section X5mod_DP_Q
open Matrix MeasureTheory Set
open scoped ComplexOrder

namespace X5DP

variable {ι κ J : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype J]

lemma Φ_psd (K : J → Matrix κ ι ℂ) {X : Matrix ι ι ℂ} (hX : X.PosSemidef) : (Φ K X).PosSemidef :=
  Matrix.posSemidef_sum _ fun j _ => hX.mul_mul_conjTranspose_same (K j)

lemma Φ_tr (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) (X : Matrix ι ι ℂ) :
    (Φ K X).trace = X.trace := by
  have := tr_dual K 1 X
  rw [Matrix.one_mul] at this
  rw [this]
  simp only [Φd, Matrix.mul_one, hK, Matrix.one_mul]

lemma Φ_supp (K : J → Matrix κ ι ℂ) {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hs : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) :
    LinearMap.ker (Φ K Y).mulVecLin ≤ LinearMap.ker (Φ K X).mulVecLin := by
  intro v hv
  rw [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
  have hq : ∀ j, star ((K j)ᴴ *ᵥ v) ⬝ᵥ Y *ᵥ ((K j)ᴴ *ᵥ v) = 0 := by
    have h0 : star v ⬝ᵥ (Φ K Y) *ᵥ v = 0 := by rw [hv, dotProduct_zero]
    have e : star v ⬝ᵥ (Φ K Y) *ᵥ v = ∑ j, star ((K j)ᴴ *ᵥ v) ⬝ᵥ Y *ᵥ ((K j)ᴴ *ᵥ v) := by
      simp only [Φ, Matrix.sum_mulVec, dotProduct_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mulVec, conjTranspose_conjTranspose, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
      try rfl
    have hn : ∀ j, 0 ≤ star ((K j)ᴴ *ᵥ v) ⬝ᵥ Y *ᵥ ((K j)ᴴ *ᵥ v) := fun j => hY.dotProduct_mulVec_nonneg _
    rw [e] at h0
    exact fun j => (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hn j).1 h0 j (Finset.mem_univ j)
  have hX0 : ∀ j, X *ᵥ ((K j)ᴴ *ᵥ v) = 0 := by
    intro j
    have h1 := (hY.dotProduct_mulVec_zero_iff _).1 (hq j)
    have := hs (show (K j)ᴴ *ᵥ v ∈ LinearMap.ker Y.mulVecLin by
      rw [LinearMap.mem_ker, mulVecLin_apply]; exact h1)
    rwa [LinearMap.mem_ker, mulVecLin_apply] at this
  simp only [Φ, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, hX0, mulVec_zero]

/-- Petz quasi-entropy with support convention. -/
noncomputable def Qf (t : ℝ) (X Y : Matrix ι ι ℂ) : ℝ :=
  (cfc (fun x : ℝ => x ^ t) X * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) Y).trace.re

lemma w_swap {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (a b : ι) :
    X5OL.w hY hX b a = X5OL.w hX hY a b := by
  have : X5OL.ov hY hX = (X5OL.ov hX hY)ᴴ := by
    simp [X5OL.ov, star_eq_conjTranspose, conjTranspose_mul]
  simp only [X5OL.w, this, conjTranspose_apply, norm_star]

lemma w_col {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (b : ι) :
    ∑ a, X5OL.w hX hY a b = 1 := by
  rw [← X5OL.w_row hY hX b]
  exact Finset.sum_congr rfl fun a _ => (w_swap hX hY a b).symm

/-- pair-sum over `μ ≠ 0` -/
noncomputable def Tset {X Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) : Finset (ι × ι) :=
  Finset.univ.filter fun k => hY.eigenvalues k.2 ≠ 0

lemma Qf_sum (t : ℝ) (ht : 1 - t ≠ 0) {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    Qf t X Y = ∑ k ∈ Tset (X := X) hY, X5OL.w hX hY k.1 k.2 *
      (hX.eigenvalues k.1 ^ t * hY.eigenvalues k.2 ^ (1 - t)) := by
  unfold Qf
  rw [X5OL.tr_cfc_cfc hX hY, Complex.re_sum]
  simp only [Complex.re_sum, Complex.ofReal_re]
  rw [← Fintype.sum_prod_type' (f := fun a b => hX.eigenvalues a ^ t *
    (if hY.eigenvalues b = 0 then 0 else hY.eigenvalues b ^ (1 - t)) * X5OL.w hX hY a b)]
  unfold Tset
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : hY.eigenvalues k.2 = 0
  · simp [h]
  · simp only [h, if_false, ne_eq, not_false_eq_true, if_true]; ring

lemma G_sum (A B : ℝ) {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (h0 : ∀ a b, hY.isHermitian.eigenvalues b = 0 →
      X5OL.w hX.isHermitian hY.isHermitian a b * hX.isHermitian.eigenvalues a ^ 2 /
        (A * hX.isHermitian.eigenvalues a + B * hY.isHermitian.eigenvalues b) = 0) :
    G A B hX.isHermitian hY.isHermitian = ∑ k ∈ Tset (X := X) hY.isHermitian,
      X5OL.w hX.isHermitian hY.isHermitian k.1 k.2 * (hX.isHermitian.eigenvalues k.1 ^ 2 /
        (A * hX.isHermitian.eigenvalues k.1 + B * hY.isHermitian.eigenvalues k.2)) := by
  unfold G Tset
  rw [← Fintype.sum_prod_type' (f := fun a b => X5OL.w hX.isHermitian hY.isHermitian a b *
    hX.isHermitian.eigenvalues a ^ 2 / (A * hX.isHermitian.eigenvalues a +
      B * hY.isHermitian.eigenvalues b)), Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · ring
  · rw [h0 k.1 k.2 (not_not.1 h)]

lemma hz {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hs : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) (a b : ι)
    (hb : hY.isHermitian.eigenvalues b = 0) :
    X5OL.w hX.isHermitian hY.isHermitian a b * hX.isHermitian.eigenvalues a ^ 2 = 0 := by
  by_cases ha : hX.isHermitian.eigenvalues a = 0
  · simp [ha]
  · simp [X5OL.w, X5OL.supp_fwd hX.isHermitian hY.isHermitian hs a b ha hb]

lemma Tpos {X Y : Matrix ι ι ℂ} (hY : Y.PosSemidef) (k : ι × ι) (hk : k ∈ Tset (X := X) hY.isHermitian) :
    0 < hY.isHermitian.eigenvalues k.2 :=
  lt_of_le_of_ne (hY.eigenvalues_nonneg _) (Finset.mem_filter.1 hk).2.symm

lemma Qf2_eq {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    Qf 2 X Y = G 0 1 hX.isHermitian hY.isHermitian := by
  unfold Qf G
  rw [X5OL.tr_cfc_cfc hX.isHermitian hY.isHermitian, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.ofReal_re, zero_mul, one_mul, zero_add, Real.rpow_two]
  norm_num
  split_ifs with h
  · simp [h]
  · rw [Real.rpow_neg_one]; field_simp

theorem Qf_gt (t : ℝ) (h1 : 1 < t) (h2 : t ≤ 2) (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1)
    {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hs : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) :
    Qf t (Φ K X) (Φ K Y) ≤ Qf t X Y := by
  have hX' := Φ_psd K hX
  have hY' := Φ_psd K hY
  have hs' := Φ_supp K hX hY hs
  have hne : 1 - t ≠ 0 := by linarith
  rcases h2.lt_or_eq with h2 | h2
  · rw [Qf_sum t hne hX'.isHermitian hY'.isHermitian, Qf_sum t hne hX.isHermitian hY.isHermitian]
    refine cmp_gen _ _ _ _ _ _ _ _ (fun x y => x ^ t * y ^ (1 - t)) (X5PQ.φ t) (X5PQ.K t)⁻¹
      (inv_nonneg.2 (X5PQ.K_pos ⟨h1, h2⟩).le) (fun x y hx hy => X5PQ.persp ⟨h1, h2⟩ hx hy)
      (fun x y hx hy => X5PQ.phi_int ⟨h1, h2⟩ hx hy)
      (fun k _ => hX'.eigenvalues_nonneg _) (fun k hk => Tpos hY' k hk)
      (fun k _ => hX.eigenvalues_nonneg _) (fun k hk => Tpos hY k hk) fun s hs0 => ?_
    have hG := G_mono K hK 1 s zero_le_one hs0.le hX hY hX' hY' (fun a b h0 => by
      have : hX.isHermitian.eigenvalues a = 0 := by
        nlinarith [hX.eigenvalues_nonneg a, mul_nonneg hs0.le (hY.eigenvalues_nonneg b)]
      simp [this])
    rw [G_sum 1 s hX' hY' (fun a b hb => by rw [hz hX' hY' hs' a b hb, zero_div]),
      G_sum 1 s hX hY (fun a b hb => by rw [hz hX hY hs a b hb, zero_div])] at hG
    have hpos : 0 ≤ s ^ (t - 2) := Real.rpow_nonneg hs0.le _
    have := mul_le_mul_of_nonneg_left hG hpos
    simp only [Finset.mul_sum, one_mul] at this
    simp only [X5PQ.φ]
    convert this using 2 <;> first | rfl | ring
  · subst h2
    rw [Qf2_eq hX' hY', Qf2_eq hX hY]
    exact G_mono K hK 0 1 le_rfl zero_le_one hX hY hX' hY' fun a b h0 => by
      have hb : hY.isHermitian.eigenvalues b = 0 := by linarith
      by_cases ha : hX.isHermitian.eigenvalues a = 0
      · simp [ha]
      · simp [X5OL.supp_fwd hX.isHermitian hY.isHermitian hs a b ha hb]

lemma sumT_mu {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    ∑ k ∈ Tset (X := X) hY, X5OL.w hX hY k.1 k.2 * hY.eigenvalues k.2 = Y.trace.re := by
  unfold Tset
  rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl (g := fun k : ι × ι => X5OL.w hX hY k.1 k.2 * hY.eigenvalues k.2)
    (fun k _ => by split_ifs with h <;> simp_all)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hY.trace_eq_sum_eigenvalues, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only
  rw [← Finset.sum_mul, w_col, one_mul]
  simp

lemma sumT_H (s : ℝ) {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    ∑ k ∈ Tset (X := X) hY.isHermitian, X5OL.w hX.isHermitian hY.isHermitian k.1 k.2 *
      (hY.isHermitian.eigenvalues k.2 ^ 2 /
        (hX.isHermitian.eigenvalues k.1 + s * hY.isHermitian.eigenvalues k.2)) =
      G s 1 hY.isHermitian hX.isHermitian := by
  unfold Tset G
  rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl (g := fun k : ι × ι => X5OL.w hX.isHermitian hY.isHermitian k.1 k.2 *
      (hY.isHermitian.eigenvalues k.2 ^ 2 /
        (hX.isHermitian.eigenvalues k.1 + s * hY.isHermitian.eigenvalues k.2)))
    (fun k _ => by split_ifs with h <;> simp_all)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [w_swap]; ring

lemma key0 (t s : ℝ) {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    ∑ k ∈ Tset (X := X) hY.isHermitian, X5OL.w hX.isHermitian hY.isHermitian k.1 k.2 *
        φ0 t s (hX.isHermitian.eigenvalues k.1) (hY.isHermitian.eigenvalues k.2) =
      s ^ (t - 1) * Y.trace.re - s ^ t * G s 1 hY.isHermitian hX.isHermitian := by
  rw [← sumT_mu hX.isHermitian hY.isHermitian, ← sumT_H s hX hY, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold φ0; ring

theorem Qf_lt (t : ℝ) (h0 : 0 < t) (h1 : t < 1) (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1)
    {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    Qf t X Y ≤ Qf t (Φ K X) (Φ K Y) := by
  have hX' := Φ_psd K hX
  have hY' := Φ_psd K hY
  have hne : 1 - t ≠ 0 := by linarith
  rw [Qf_sum t hne hX'.isHermitian hY'.isHermitian, Qf_sum t hne hX.isHermitian hY.isHermitian]
  refine cmp_gen _ _ _ _ _ _ _ _ (fun x y => x ^ t * y ^ (1 - t)) (φ0 t)
    (∫ s in Ioi 0, Real.rpowIntegrand₀₁ t s 1)⁻¹ (inv_nonneg.2 (K0_pos ⟨h0, h1⟩).le)
    (fun x y hx hy => persp0 ⟨h0, h1⟩ hx hy) (fun x y hx hy => phi0_int ⟨h0, h1⟩ hx hy)
    (fun k _ => hX.eigenvalues_nonneg _) (fun k hk => Tpos hY k hk)
    (fun k _ => hX'.eigenvalues_nonneg _) (fun k hk => Tpos hY' k hk) fun s hs0 => ?_
  have hG := G_mono K hK s 1 hs0.le zero_le_one hY hX hY' hX' (fun a b h0 => by
    have : hY.isHermitian.eigenvalues a = 0 := by
      nlinarith [hY.eigenvalues_nonneg a, hX.eigenvalues_nonneg b, mul_nonneg hs0.le (hY.eigenvalues_nonneg a)]
    simp [this])
  rw [key0 t s hX hY, key0 t s hX' hY', Φ_tr K hK]
  have hpos : 0 ≤ s ^ t := Real.rpow_nonneg hs0.le _
  nlinarith [mul_le_mul_of_nonneg_left hG hpos]

end X5DP
end X5mod_DP_Q

section X5mod_DP_Thm
open Matrix Filter Set
open scoped ComplexOrder Kronecker Topology ENNReal

namespace X5DP
set_option linter.unusedSectionVars false
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B]
  [DecidableEq C]

lemma hk {m n p q : Type*} (X : Matrix m n ℂ) (Y : Matrix p q ℂ) : Matrix.kronecker X Y = X ⊗ₖ Y := rfl

lemma kron_sum {m : ℕ} (f : Fin m → Matrix C C ℂ) :
    ∑ j, Matrix.kronecker (1 : Matrix A A ℂ) (f j) = Matrix.kronecker (1 : Matrix A A ℂ) (∑ j, f j) := by
  ext p q
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]

lemma kraus_id (E : Superop B C) {m : ℕ} (E' : Fin m → Matrix C B ℂ) (hK : ∑ j, (E' j)ᴴ * E' j = 1)
    (hE : ∀ ρ, E ρ = krausApply E' ρ) :
    (∑ j, (Matrix.kronecker (1 : Matrix A A ℂ) (E' j))ᴴ * Matrix.kronecker (1 : Matrix A A ℂ) (E' j) = 1) ∧
    (∀ X, idTensorSuperop (R := A) E X = Φ (fun j => Matrix.kronecker (1 : Matrix A A ℂ) (E' j)) X) ∧
    (∀ σ, Φ (fun j => Matrix.kronecker (1 : Matrix A A ℂ) (E' j)) (identityTensorReference (A := A) σ) =
      identityTensorReference (A := A) (E σ)) := by
  refine ⟨?_, ?_, ?_⟩
  · have : ∀ j, (Matrix.kronecker (1 : Matrix A A ℂ) (E' j))ᴴ * Matrix.kronecker (1 : Matrix A A ℂ) (E' j) =
        Matrix.kronecker (1 : Matrix A A ℂ) ((E' j)ᴴ * E' j) := by
      intro j
      simp only [hk]
      rw [Matrix.conjTranspose_kronecker, conjTranspose_one]
      have := Matrix.mul_kronecker_mul (1 : Matrix A A ℂ) (1 : Matrix A A ℂ) (E' j)ᴴ (E' j)
      rw [Matrix.mul_one] at this
      exact this.symm
    rw [Finset.sum_congr rfl fun j _ => this j, kron_sum, hK]
    exact Matrix.one_kronecker_one
  · intro X
    ext p q
    simp only [idTensorSuperop, Matrix.of_apply]
    rw [hE]
    simp only [Φ, krausApply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hs : ∀ (c : Prop) [Decidable c], star (if c then (1:ℂ) else 0) = if c then 1 else 0 := by
      intro c _; split_ifs <;> simp
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.of_apply, Fintype.sum_prod_type, one_apply, star_mul', hs]
    simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true, Finset.sum_ite_eq]
  · intro σ
    have : ∀ j, Matrix.kronecker (1 : Matrix A A ℂ) (E' j) * identityTensorReference (A := A) σ *
        (Matrix.kronecker (1 : Matrix A A ℂ) (E' j))ᴴ =
        Matrix.kronecker (1 : Matrix A A ℂ) (E' j * σ * (E' j)ᴴ) := by
      intro j
      unfold identityTensorReference
      simp only [hk]
      rw [Matrix.conjTranspose_kronecker, conjTranspose_one]
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.mul_one]
    unfold Φ
    rw [Finset.sum_congr rfl fun j _ => this j, kron_sum, hE]
    rfl

lemma Qf_nonneg (t : ℝ) (ht : 1 - t ≠ 0) {ι : Type*} [Fintype ι] [DecidableEq ι] {X Y : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : 0 ≤ Qf t X Y := by
  rw [Qf_sum t ht hX.isHermitian hY.isHermitian]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (X5OL.w_nonneg _ _ _ _)
    (mul_nonneg (Real.rpow_nonneg (hX.eigenvalues_nonneg _) _) (Real.rpow_nonneg (hY.eigenvalues_nonneg _) _))

lemma N_psd (σ : Matrix B B ℂ) (hσ : σ.PosSemidef) : (identityTensorReference (A := A) σ).PosSemidef := by
  unfold identityTensorReference
  exact Matrix.PosSemidef.one.kronecker hσ

lemma fa_eq (ρ : Matrix (A × B) (A × B) ℂ) (σ : Matrix B B ℂ) (t : ℝ) (ht : t ≠ 1) :
    finiteAlpha ρ σ t = if 1 < t ∧ ¬ supportedBy ρ (identityTensorReference (A := A) σ) then ⊥
      else ((1 / (1 - t) : ℝ) : EReal) * log2Extended (Qf t ρ (identityTensorReference (A := A) σ)) := by
  unfold finiteAlpha
  rw [if_neg ht]
  rfl

lemma L_pos {x : ℝ} (hx : 0 < x) : log2Extended x = ((Real.logb 2 x : ℝ) : EReal) := by
  unfold log2Extended; rw [if_neg hx.ne']

section main
variable [Nonempty A] [Nonempty B] [Nonempty C]

theorem fa_le (ρ : Matrix (A × B) (A × B) ℂ) (σ : Matrix B B ℂ) (hρ : IsDensityMatrix ρ)
    (hσ : IsDensityMatrix σ) (E : Superop B C) (hE : IsChannel E)
    (t : ℝ) (h0 : 0 < t) (h2 : t ≤ 2) (h1 : t ≠ 1) :
    finiteAlpha ρ σ t ≤ finiteAlpha (idTensorSuperop (R := A) E ρ) (E σ) t := by
  obtain ⟨m, E', hK, hEq⟩ := hE
  obtain ⟨hK2, hid, hN⟩ := kraus_id (A := A) E E' hK hEq
  set K := fun j => Matrix.kronecker (1 : Matrix A A ℂ) (E' j)
  have hNσ : identityTensorReference (A := A) (E σ) = Φ K (identityTensorReference (A := A) σ) :=
    (hN σ).symm
  rw [fa_eq _ _ t h1, fa_eq _ _ t h1, hid ρ, hNσ]
  have hNpsd := N_psd (A := A) σ hσ.1
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · rw [if_neg (fun h => by linarith [h.1]), if_neg (fun h => by linarith [h.1])]
    have hQ := Qf_lt t h0 hlt K hK2 hρ.1 hNpsd
    have hQ0 := Qf_nonneg t (by linarith) hρ.1 hNpsd
    have hc : (0:ℝ) < 1 / (1 - t) := by apply div_pos one_pos; linarith
    rcases hQ0.lt_or_eq with hpos | hzero
    · rw [L_pos hpos, L_pos (hpos.trans_le hQ), ← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      exact mul_le_mul_of_nonneg_left (Real.logb_le_logb_of_le (by norm_num) hpos hQ) hc.le
    · rw [← hzero]
      unfold log2Extended
      rw [if_pos rfl, EReal.coe_mul_bot_of_pos hc]
      exact bot_le
  · by_cases hs : supportedBy ρ (identityTensorReference (A := A) σ)
    · have hs' := Φ_supp K hρ.1 hNpsd hs
      rw [if_neg (fun h => h.2 hs), if_neg (fun h => h.2 hs')]
      have hQ := Qf_gt t hgt h2 K hK2 hρ.1 hNpsd hs
      have hQ0 := Qf_nonneg t (by linarith) (Φ_psd K hρ.1) (Φ_psd K hNpsd)
      have hc : 1 / (1 - t) < (0:ℝ) := by apply div_neg_of_pos_of_neg one_pos; linarith
      rcases hQ0.lt_or_eq with hpos | hzero
      · rw [L_pos hpos, L_pos (hpos.trans_le hQ), ← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_le_coe_iff]
        exact mul_le_mul_of_nonpos_left (Real.logb_le_logb_of_le (by norm_num) hpos hQ) hc.le
      · rw [← hzero]
        unfold log2Extended
        rw [if_pos rfl, EReal.coe_mul_bot_of_neg hc]
        exact le_top
    · rw [if_pos ⟨hgt, hs⟩]; exact bot_le

lemma dens (ρ : Matrix (A × B) (A × B) ℂ) (σ : Matrix B B ℂ) (hρ : IsDensityMatrix ρ)
    (hσ : IsDensityMatrix σ) (E : Superop B C) (hE : IsChannel E) :
    IsDensityMatrix (idTensorSuperop (R := A) E ρ) ∧ IsDensityMatrix (E σ) := by
  obtain ⟨m, E', hK, hEq⟩ := hE
  obtain ⟨hK2, hid, -⟩ := kraus_id (A := A) E E' hK hEq
  refine ⟨?_, ?_⟩
  · rw [hid ρ]; exact ⟨Φ_psd _ hρ.1, by rw [Φ_tr _ hK2]; exact hρ.2⟩
  · rw [hEq σ]; exact ⟨Φ_psd E' hσ.1, by rw [show krausApply E' σ = Φ E' σ from rfl, Φ_tr _ hK]; exact hσ.2⟩

theorem fa_one (ρ : Matrix (A × B) (A × B) ℂ) (σ : Matrix B B ℂ) (hρ : IsDensityMatrix ρ)
    (hσ : IsDensityMatrix σ) (E : Superop B C) (hE : IsChannel E) :
    fixedVonNeumann ρ σ ≤ fixedVonNeumann (idTensorSuperop (R := A) E ρ) (E σ) := by
  obtain ⟨hτ, hω⟩ := dens ρ σ hρ hσ E hE
  have L1 := (alphaOneLimit ρ σ hρ hσ).1
  have L2 := (alphaOneLimit _ _ hτ hω).1
  have hcl : (1 : ℝ) ∈ closure {t : ℝ | 0 < t ∧ t ≠ 1} := by
    have : Ioo (0:ℝ) 1 ⊆ {t : ℝ | 0 < t ∧ t ≠ 1} := fun t ht => ⟨ht.1, ht.2.ne⟩
    refine closure_mono this ?_
    rw [closure_Ioo zero_ne_one]
    exact ⟨zero_le_one, le_rfl⟩
  haveI := mem_closure_iff_nhdsWithin_neBot.1 hcl
  refine le_of_tendsto_of_tendsto L1 L2 ?_
  filter_upwards [inter_mem_nhdsWithin {t : ℝ | 0 < t ∧ t ≠ 1} (Iio_mem_nhds (by norm_num : (1:ℝ) < 2)),
    self_mem_nhdsWithin] with t ht ht'
  exact fa_le ρ σ hρ hσ E hE t ht'.1 (le_of_lt ht.2) ht'.2

end main

end X5DP
end X5mod_DP_Thm

section X5mod_RB_Base
open Matrix
open scoped ComplexOrder

namespace X5RB
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23
open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)
open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

section
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

noncomputable def rx (e : m ≃ n) : Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ :=
  { (Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom with
    map_star' := fun X => by
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex] }

lemma rx_apply (e : m ≃ n) (X : Matrix m m ℂ) : rx e X = reindex e e X := rfl

lemma rmul (e : m ≃ n) (X Y : Matrix m m ℂ) : reindex e e X * reindex e e Y = reindex e e (X * Y) := by
  rw [← rx_apply, ← rx_apply, ← rx_apply, map_mul]

lemma tr_rx (e : m ≃ n) (X : Matrix m m ℂ) : (reindex e e X).trace = X.trace := by
  simp only [Matrix.trace, diag_apply, reindex_apply, submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => X i i)

lemma sa_rx (e : m ≃ n) (X : Matrix m m ℂ) : IsSelfAdjoint (reindex e e X) ↔ IsSelfAdjoint X := by
  constructor
  · intro h
    have : reindex e.symm e.symm (reindex e e X) = X := by ext; simp [reindex_apply]
    rw [← this]
    have h' : (reindex e.symm e.symm (reindex e e X))ᴴ = reindex e.symm e.symm (reindex e e X) := by
      rw [Matrix.conjTranspose_reindex]; exact congrArg _ h
    exact h'
  · intro h
    have h' : (reindex e e X)ᴴ = reindex e e X := by rw [Matrix.conjTranspose_reindex]; exact congrArg _ h
    exact h'

lemma cfc_rx (e : m ≃ n) (X : Matrix m m ℂ) (f : ℝ → ℝ) :
    cfc f (reindex e e X) = reindex e e (cfc f X) := by
  by_cases hX : IsSelfAdjoint X
  · have hc : Continuous (rx e) := by
      change Continuous fun X : Matrix m m ℂ => reindex e e X
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [reindex_apply, submatrix_apply]
      exact (continuous_apply _).comp (continuous_apply _)
    have h := StarAlgHom.map_cfc (R := ℝ) (S := ℂ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
      (rx e) f X (X.finite_real_spectrum.continuousOn _) hc hX ((sa_rx e X).2 hX)
    exact h.symm
  · rw [cfc_apply_of_not_predicate X hX, cfc_apply_of_not_predicate _ (fun h => hX ((sa_rx e X).1 h))]
    ext; simp [reindex_apply]

lemma psd_rx (e : m ≃ n) (X : Matrix m m ℂ) : (reindex e e X).PosSemidef ↔ X.PosSemidef := by
  rw [reindex_apply]; exact posSemidef_submatrix_equiv e.symm

lemma supp_rx (e : m ≃ n) (X Y : Matrix m m ℂ) :
    supportedBy (reindex e e X) (reindex e e Y) ↔ supportedBy X Y := by
  have key : ∀ (M : Matrix m m ℂ) (v : n → ℂ), reindex e e M *ᵥ v = (M *ᵥ (v ∘ e)) ∘ e.symm := by
    intro M v; ext i
    simp only [mulVec, dotProduct, reindex_apply, submatrix_apply, Function.comp_apply]
    exact (Equiv.sum_comp e.symm (fun j => M (e.symm i) j * v (e j))).symm.trans (by simp) |>.symm
  have key0 : ∀ (M : Matrix m m ℂ) (v : n → ℂ), reindex e e M *ᵥ v = 0 ↔ M *ᵥ (v ∘ e) = 0 := by
    intro M v; rw [key]; constructor
    · intro h; ext j; have := congrFun h (e j); simpa using this
    · intro h; rw [h]; rfl
  unfold supportedBy
  constructor
  · intro h x hx
    rw [LinearMap.mem_ker, mulVecLin_apply] at hx ⊢
    have h1 : x ∘ e.symm ∘ e = x := by ext; simp
    have := h (show x ∘ e.symm ∈ LinearMap.ker (reindex e e Y).mulVecLin by
      rw [LinearMap.mem_ker, mulVecLin_apply, key0, Function.comp_assoc, h1]; exact hx)
    rw [LinearMap.mem_ker, mulVecLin_apply, key0, Function.comp_assoc, h1] at this
    exact this
  · intro h x hx
    rw [LinearMap.mem_ker, mulVecLin_apply, key0] at hx ⊢
    exact h hx
end

section
variable {A A' B : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B]

end

end X5RB
end X5mod_RB_Base

section X5mod_B2_Main
open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace X5B2

section Scalar
variable {ι : Type*} [Fintype ι]
variable {l m : ι → ℝ} {W : ι → ι → ℝ}

noncomputable def Tset (l : ι → ℝ) (W : ι → ι → ℝ) : Finset (ι × ι) :=
  univ.filter fun p => W p.1 p.2 ≠ 0 ∧ l p.2 ≠ 0

variable (hW : ∀ i j, 0 ≤ W i j) (hcol : ∀ j, ∑ i, W i j = 1) (hl : ∀ j, 0 ≤ l j)
  (hm : ∀ i, 0 ≤ m i) (hs : ∀ i j, W i j ≠ 0 → l j ≠ 0 → m i ≠ 0)

end Scalar

section Mat
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma psd_re {X : Matrix I I ℂ} (h : X.PosSemidef) : 0 ≤ X.trace.re :=
  (Complex.nonneg_iff.mp h.trace_nonneg).1

lemma fin (X : Matrix I I ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma cs (X Y : Matrix I I ℂ) :
    (Xᴴ * Y).trace.re + (Yᴴ * X).trace.re ≤ (Xᴴ * X).trace.re + (Yᴴ * Y).trace.re := by
  have h0 := psd_re (Matrix.posSemidef_conjTranspose_mul_self (X - Y))
  simp only [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
    Complex.sub_re] at h0
  linarith

lemma w_swap {X Y : Matrix I I ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (a b : I) :
    X5OL.w hY hX b a = X5OL.w hX hY a b := by
  have : X5OL.ov hY hX = (X5OL.ov hX hY)ᴴ := by
    simp [X5OL.ov, star_eq_conjTranspose, conjTranspose_mul]
  simp only [X5OL.w, this, conjTranspose_apply, norm_star]

lemma w_col {X Y : Matrix I I ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (b : I) :
    ∑ a, X5OL.w hX hY a b = 1 := by
  rw [← X5OL.w_row hY hX b]
  exact Finset.sum_congr rfl fun a _ => (w_swap hX hY a b).symm

end Mat

end X5B2

namespace X5B2
open QAlgorithms.Papers.Independent.Claimed50.P12

variable {I : Type*} [Fintype I] [DecidableEq I]

end X5B2
end X5mod_B2_Main

section X5mod_UH_Base
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder

namespace X5UH
set_option linter.unusedSectionVars false

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

end X5UH
end X5mod_UH_Base

section X5mod_UH_Polar
open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace X5UH
set_option linter.unusedSectionVars false

variable {R : Type*} [Fintype R] [DecidableEq R]

end X5UH
end X5mod_UH_Polar

section X5mod_UH_Main
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate

namespace X5UH
set_option linter.unusedSectionVars false

variable {D R : Type*} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

end X5UH
end X5mod_UH_Main

section X5mod_UH_Thm
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate

namespace X5UH
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Information100.P32 (Op)
set_option linter.unusedSectionVars false

variable {D R : Type*} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

end X5UH
end X5mod_UH_Thm

section X5mod_UH_B4
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5UH
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Information100.P32 (Op)
set_option linter.unusedSectionVars false

variable {D E X : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
  [Fintype X] [DecidableEq X]

end X5UH
end X5mod_UH_B4

section X5mod_UH_B5
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5UH
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Information100.P32 (Op)
set_option linter.unusedSectionVars false

variable {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R]

end X5UH
end X5mod_UH_B5

section X5mod_UH_B8a
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5UH
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Information100.P32 (Op)
set_option linter.unusedSectionVars false

variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

end X5UH
end X5mod_UH_B8a

section X5mod_UH_B8
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5UH
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Information100.P32 (Op)
set_option linter.unusedSectionVars false

variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

end X5UH
end X5mod_UH_B8

section X5mod_AI_Base
open Matrix

section X5mod_AI_Base

/-- conjugation by an isometry as a non-unital star algebra hom -/
noncomputable def x5ai_conjHom {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix n m ℂ) (hW : Wᴴ * W = 1) : Matrix m m ℂ →⋆ₙₐ[ℂ] Matrix n n ℂ where
  toFun X := W * X * Wᴴ
  map_smul' c X := by simp
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_mul' X Y := by
    calc W * (X * Y) * Wᴴ = W * X * (Wᴴ * W) * Y * Wᴴ := by rw [hW]; simp [Matrix.mul_assoc]
      _ = _ := by simp [Matrix.mul_assoc]
  map_star' X := by simp [Matrix.star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc]

theorem x5ai_finite_cont {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (quasispectrum ℝ M) := by
  have : (quasispectrum ℝ M).Finite := by
    rw [quasispectrum_eq_spectrum_union_zero]
    exact (M.finite_real_spectrum).union (Set.finite_singleton 0)
  exact this.continuousOn _

theorem x5ai_conj {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix n m ℂ) (hW : Wᴴ * W = 1) (M : Matrix m m ℂ) (hM : M.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) : cfc f (W * M * Wᴴ) = W * cfc f M * Wᴴ := by
  have hWM : (W * M * Wᴴ).IsHermitian := by
    simp [IsHermitian, conjTranspose_mul, hM.eq, Matrix.mul_assoc]
  have hc : Continuous (x5ai_conjHom W hW) := by
    change Continuous fun X : Matrix m m ℂ => W * X * Wᴴ; fun_prop
  have h := NonUnitalStarAlgHom.map_cfcₙ (R := ℝ) (S := ℂ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (x5ai_conjHom W hW) f M (x5ai_finite_cont M f) hf hc hM.isSelfAdjoint hWM.isSelfAdjoint
  have h2 : W * cfcₙ f M * Wᴴ = cfcₙ f (W * M * Wᴴ) := h
  have e1 : cfcₙ f M = cfc f M := cfcₙ_eq_cfc (x5ai_finite_cont M f) hf
  have e2 : cfcₙ f (W * M * Wᴴ) = cfc f (W * M * Wᴴ) := cfcₙ_eq_cfc (x5ai_finite_cont (W * M * Wᴴ) f) hf
  rw [← e1, ← e2, h2]

end X5mod_AI_Base
end X5mod_AI_Base

section X5mod_AD_Kron
open Matrix Polynomial
open scoped ComplexOrder Kronecker

namespace X5AD
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma aeval_diag (δ : ι → ℂ) (p : ℝ[X]) :
    aeval (diagonal δ) p = diagonal (fun k => aeval (δ k) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, diagonal_add]
  | monomial k c =>
    simp only [aeval_monomial, Matrix.algebraMap_eq_diagonal, diagonal_pow, diagonal_mul_diagonal]
    rfl

lemma cfc_diag (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun k => ((d k : ℝ) : ℂ))) = diagonal (fun k => ((f (d k) : ℝ) : ℂ)) := by
  set D := diagonal (fun k => ((d k : ℝ) : ℂ))
  have hfin : (spectrum ℝ D).Finite := D.finite_real_spectrum
  set s : Finset ℝ := Finset.univ.image d ∪ hfin.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have hD : IsSelfAdjoint D := by
    rw [← Matrix.isHermitian_iff_isSelfAdjoint]
    exact isHermitian_diagonal_of_self_adjoint _ (by ext k; simp [Complex.conj_ofReal])
  have h1 : cfc f D = cfc (fun x => p.eval x) D :=
    cfc_congr fun x hx => (hp x (Finset.mem_union_right _ (hfin.mem_toFinset.2 hx))).symm
  rw [h1, cfc_polynomial p D hD, aeval_diag]
  congr 1; ext k
  rw [show ((d k : ℝ) : ℂ) = algebraMap ℝ ℂ (d k) from rfl, aeval_algebraMap_apply,
    Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval,
    hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))]
  rfl

lemma spec {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun k => ((hX.eigenvalues k : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  conv_lhs => rw [← cfc_id' ℝ X hX.isSelfAdjoint]
  rw [hX.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma cfc_spec {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    cfc f X = (hX.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun k => ((f (hX.eigenvalues k) : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  rw [hX.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma uu {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * (hX.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
  Unitary.coe_star_mul_self _

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

end X5AD
end X5mod_AD_Kron

section X5mod_QC_Emb
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
set_option linter.unusedSectionVars false

variable {m n K : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype K]
  [DecidableEq K]

/-- A family of orthogonal multiplicative embeddings. -/
structure OEmb (E : K → Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop where
  mul : ∀ b c Y Z, E b Y * E c Z = if b = c then E b (Y * Z) else 0
  star : ∀ b Y, (E b Y)ᴴ = E b Yᴴ

variable {E : K → Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ}

lemma OEmb.herm (hE : OEmb E) {Y : K → Matrix m m ℂ} (hY : ∀ b, (Y b).IsHermitian) :
    (∑ b, E b (Y b)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hE.star, (hY b).eq]

end X5QC

namespace X5QC
set_option linter.unusedSectionVars false
variable {m n B : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype B]
  [DecidableEq B]

end X5QC
end X5mod_QC_Emb

section X5mod_QC_Kron
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

open X5AD in
theorem cfc_kron2 {X : Matrix ι ι ℂ} {Y : Matrix κ κ ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (f g1 h1 g2 h2 : ℝ → ℝ) (hf0 : f 0 = 0)
    (hsplit : ∀ x y, 0 ≤ x → 0 ≤ y → f (x * y) = g1 x * h1 y + g2 x * h2 y) :
    cfc f (X ⊗ₖ Y) = cfc g1 X ⊗ₖ cfc h1 Y + cfc g2 X ⊗ₖ cfc h2 Y := by
  have hXh := hX.isHermitian
  have hYh := hY.isHermitian
  set U := (hXh.eigenvectorUnitary : Matrix ι ι ℂ)
  set V := (hYh.eigenvectorUnitary : Matrix κ κ ℂ)
  set d := hXh.eigenvalues
  set e := hYh.eigenvalues
  have hW : (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, uu hXh, uu hYh, one_kronecker_one]
  have hDE : diagonal (fun k => ((d k : ℝ) : ℂ)) ⊗ₖ diagonal (fun k => ((e k : ℝ) : ℂ)) =
      diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ)) := by
    rw [diagonal_kronecker_diagonal]; congr 1; ext p; simp
  have hXY : X ⊗ₖ Y = (U ⊗ₖ V) * diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ)) * (U ⊗ₖ V)ᴴ := by
    conv_lhs => rw [spec hXh, spec hYh]
    rw [← hDE, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]
  have hDh : (diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ))).IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ (by ext k; simp [Complex.conj_ofReal])
  rw [hXY, x5ai_conj (U ⊗ₖ V) hW _ hDh f hf0, cfc_diag (fun p : ι × κ => d p.1 * e p.2) f,
    cfc_spec hXh, cfc_spec hYh, cfc_spec hXh, cfc_spec hYh]
  have hd : ∀ k, 0 ≤ d k := hX.eigenvalues_nonneg
  have he : ∀ k, 0 ≤ e k := hY.eigenvalues_nonneg
  have hDE' : diagonal (fun p : ι × κ => ((f (d p.1 * e p.2) : ℝ) : ℂ)) =
      diagonal (fun k => ((g1 (d k) : ℝ) : ℂ)) ⊗ₖ diagonal (fun k => ((h1 (e k) : ℝ) : ℂ)) +
      diagonal (fun k => ((g2 (d k) : ℝ) : ℂ)) ⊗ₖ diagonal (fun k => ((h2 (e k) : ℝ) : ℂ)) := by
    rw [diagonal_kronecker_diagonal, diagonal_kronecker_diagonal, diagonal_add]; congr 1; ext p
    simp [hsplit _ _ (hd p.1) (he p.2)]
  rw [hDE', Matrix.mul_add, Matrix.add_mul, conjTranspose_kronecker, ← mul_kronecker_mul,
    ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul]

end X5QC
end X5mod_QC_Kron

section X5mod_QC_Supp
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def ind (x : ℝ) : ℝ := if x = 0 then 0 else 1

noncomputable def supp (X : Matrix ι ι ℂ) : Matrix ι ι ℂ := cfc ind X

end X5QC
end X5mod_QC_Supp

section X5mod_QC_Qcq
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
set_option linter.unusedSectionVars false

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

variable (U : Matrix B B ℂ) (p : B → ℝ) (rho : B → Matrix (A × C) (A × C) ℂ)

end X5QC
end X5mod_QC_Qcq

section X5mod_QC_Ent
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma real_smul (p : ℝ) (Y : Matrix ι ι ℂ) : (p : ℂ) • Y = p • Y := by
  ext i j; simp [Complex.real_smul]

lemma cfc_log_smul {p : ℝ} (hp : 0 < p) (Y : Matrix ι ι ℂ) (hY : Y.IsHermitian) :
    cfc Real.log ((p : ℂ) • Y) = ((Real.log p : ℝ) : ℂ) • supp Y + cfc Real.log Y := by
  rw [real_smul, ← cfc_comp_smul p _ Y ((Y.finite_real_spectrum.image _).continuousOn _) hY.isSelfAdjoint, real_smul, supp,
    ← cfc_smul _ _ _ (X5B2.fin _ _), ← cfc_add _ _ _ (X5B2.fin _ _) (X5B2.fin _ _)]
  refine cfc_congr fun x _ => ?_
  simp only [smul_eq_mul, ind]
  by_cases hx : x = 0
  · subst hx; simp
  rw [if_neg hx, Real.log_mul hp.ne' hx]; ring

lemma log_kron {Y : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ} (hY : Y.PosSemidef) (hZ : Z.PosSemidef) :
    cfc Real.log (Y ⊗ₖ Z) = cfc Real.log Y ⊗ₖ supp Z + supp Y ⊗ₖ cfc Real.log Z :=
  cfc_kron2 hY hZ Real.log Real.log ind ind Real.log Real.log_zero (fun x y _ _ => by
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [ind, hx, hy, Real.log_mul])

/-- `Tr (X log X)`, in nats. -/
noncomputable def T (X : Matrix ι ι ℂ) : ℝ := (cfc (fun x : ℝ => x * Real.log x) X).trace.re

lemma vn_eq (X : Matrix ι ι ℂ) : QAlgorithms.vnEntropy X = -T X / Real.log 2 := by
  unfold QAlgorithms.vnEntropy T
  have : cfc (fun x : ℝ => x * Real.logb 2 x) X =
      ((Real.log 2)⁻¹ : ℝ) • cfc (fun x : ℝ => x * Real.log x) X := by
    rw [← cfc_smul _ _ _ (X5B2.fin _ _)]
    refine cfc_congr fun x _ => ?_
    simp only [smul_eq_mul, Real.logb]; ring
  rw [this, Matrix.trace_smul]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  ring

end X5QC
end X5mod_QC_Ent

section X5mod_QC_Blk
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
set_option linter.unusedSectionVars false

section gen
variable {m n K : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype K]
  [DecidableEq K] {E : K → Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ}

end gen

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma mul_log (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    X * cfc Real.log X = cfc (fun x : ℝ => x * Real.log x) X := by
  nth_rewrite 1 [← cfc_id' ℝ X hX.isSelfAdjoint]
  rw [← cfc_mul _ _ _ (X5B2.fin _ _) (X5B2.fin _ _)]

end X5QC
end X5mod_QC_Blk

section X5mod_QC_Main
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
set_option linter.unusedSectionVars false

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
variable {U : Matrix B B ℂ} (hU : Uᴴ * U = 1) {p : B → ℝ} (hp : ∀ b, 0 ≤ p b)
  {rho : B → Matrix (A × C) (A × C) ℂ} (hrho : ∀ b, QAlgorithms.IsDensityMatrix (rho b))
include hU hp hrho

end X5QC
end X5mod_QC_Main

section X5mod_QC_Thm
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
set_option linter.unusedSectionVars false

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

variable (U : Matrix B B ℂ) (p : B → ℝ) (rho : B → Matrix (A × C) (A × C) ℂ)

end X5QC
end X5mod_QC_Thm

section X5mod_QC_Final
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
set_option linter.unusedSectionVars false

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

end X5QC
end X5mod_QC_Final

section X5mod_QC_Conc
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
set_option linter.unusedSectionVars false

variable {A B X : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype X] [DecidableEq X]

variable (p : X → ℝ) (rho : X → Matrix (A × B) (A × B) ℂ)

variable {p rho}

end X5QC
end X5mod_QC_Conc

section X5mod_QC_Mix
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QC
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
set_option linter.unusedSectionVars false

variable {A X : Type*} [Fintype A] [DecidableEq A] [Fintype X] [DecidableEq X]

variable (p : X → ℝ) (rho : X → Matrix A A ℂ)

variable {p rho}

end X5QC
end X5mod_QC_Mix

section X5mod_AF_Bounds
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5AF
open X5QC
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma tr_cfc {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    (cfc f X).trace = ∑ i, ((f (hX.eigenvalues i) : ℝ) : ℂ) := by
  rw [hX.cfc_eq]
  unfold IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply]
  set U := (hX.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (hX.eigenvectorUnitary).2
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]
  rfl

/-! transpose invariance -/

end X5AF
end X5mod_AF_Bounds

section X5mod_AF_Cond
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5AF
open X5QC
set_option linter.unusedSectionVars false

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

end X5AF
end X5mod_AF_Cond

section X5mod_AF_Mix2
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5AF
open X5QC
set_option linter.unusedSectionVars false

variable {A B X : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype X] [DecidableEq X]

end X5AF
end X5mod_AF_Mix2

section X5mod_QK_Vec
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QK
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

end X5QK
end X5mod_QK_Vec

section X5mod_QK_Ops
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QK
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

end X5QK
end X5mod_QK_Ops

section X5mod_QK_Pure
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QK
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

end X5QK
end X5mod_QK_Pure

section X5mod_QK_Main
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QK
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

end X5QK
end X5mod_QK_Main

section X5mod_AF_Main
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5AF
open X5QC
set_option linter.unusedSectionVars false

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

end X5AF
end X5mod_AF_Main

section X5mod_AF_Fannes

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms

namespace X5AF

end X5AF
end X5mod_AF_Fannes

section X5mod_AF_Reindex
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5AF
open X5QC
set_option linter.unusedSectionVars false

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

lemma trace_sub_equiv (e : n ≃ m) (X : Matrix m m ℂ) : (X.submatrix e e).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun j => X j j)

lemma aeval_sub_equiv (e : n ≃ m) (X : Matrix m m ℂ) (p : ℝ[X]) :
    aeval (X.submatrix e e) p = (aeval X p).submatrix e e := by
  have h := Polynomial.aeval_algHom_apply (Matrix.reindexAlgEquiv ℝ ℂ e.symm) X p
  simpa [Matrix.reindexAlgEquiv, Matrix.reindex_apply] using h

lemma tr_cfc_sub {X : Matrix m m ℂ} (hX : X.IsHermitian) (e : n ≃ m) (f : ℝ → ℝ) :
    (cfc f (X.submatrix e e)).trace = (cfc f X).trace := by
  have hA : IsSelfAdjoint (X.submatrix e e) := (hX.submatrix e).isSelfAdjoint
  have hB : IsSelfAdjoint X := hX.isSelfAdjoint
  have fA : (spectrum ℝ (X.submatrix e e)).Finite := (X.submatrix e e).finite_real_spectrum
  have fB : (spectrum ℝ X).Finite := X.finite_real_spectrum
  set s : Finset ℝ := fA.toFinset ∪ fB.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have h1 : cfc f (X.submatrix e e) = cfc (fun x => p.eval x) (X.submatrix e e) :=
    cfc_congr fun x hx => (hp x (by simp [s, fA.mem_toFinset.2 hx])).symm
  have h2 : cfc f X = cfc (fun x => p.eval x) X :=
    cfc_congr fun x hx => (hp x (by simp [s, fB.mem_toFinset.2 hx])).symm
  rw [h1, h2, cfc_polynomial p _ hA, cfc_polynomial p X hB, aeval_sub_equiv, trace_sub_equiv]

lemma traceNorm_sub (Z : Matrix m m ℂ) (e : n ≃ m) :
    QAlgorithms.traceNorm (Z.submatrix e e) = QAlgorithms.traceNorm Z := by
  unfold QAlgorithms.traceNorm
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    tr_cfc_sub (Matrix.isHermitian_conjTranspose_mul_self Z)]

lemma dens_sub {X : Matrix m m ℂ} (hX : QAlgorithms.IsDensityMatrix X) (e : n ≃ m) :
    QAlgorithms.IsDensityMatrix (X.submatrix e e) :=
  ⟨hX.1.submatrix e, (trace_sub_equiv e X).trans hX.2⟩

end X5AF
end X5mod_AF_Reindex

section X5mod_PK_Base
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- cfc of a Hermitian matrix is the aeval of any interpolating polynomial on a superset
of its spectrum. -/
lemma cfc_eq_interp {Y : Matrix n n ℂ} (hY : Y.IsHermitian) (S : Finset ℝ)
    (hS : spectrum ℝ Y ⊆ S) (f : ℝ → ℝ) :
    cfc f Y = aeval Y (Lagrange.interpolate S (fun x : ℝ => x) f) := by
  set p := Lagrange.interpolate S (fun x : ℝ => x) f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  rw [← cfc_polynomial p Y hY.isSelfAdjoint]
  exact cfc_congr fun x hx => (hp x (hS hx)).symm

lemma spec_fin (Y : Matrix n n ℂ) : spectrum ℝ Y ⊆ (Y.finite_real_spectrum).toFinset := by
  intro x hx; simpa using hx

/-- Transfer of cfc along any map that intertwines polynomial evaluation. -/
lemma cfc_transfer {X : Matrix m m ℂ} {Y : Matrix n n ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (G : Matrix m m ℂ → Matrix n n ℂ)
    (hG : ∀ p : ℝ[X], aeval Y p = G (aeval X p)) (f : ℝ → ℝ) :
    cfc f Y = G (cfc f X) := by
  set S := (X.finite_real_spectrum).toFinset ∪ (Y.finite_real_spectrum).toFinset
  rw [cfc_eq_interp hY S ((spec_fin Y).trans subset_union_right),
    cfc_eq_interp hX S ((spec_fin X).trans subset_union_left), hG]

lemma cfc_conj (U : unitary (Matrix n n ℂ)) {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (f : ℝ → ℝ) :
    cfc f ((U : Matrix n n ℂ) * X * star (U : Matrix n n ℂ)) =
      (U : Matrix n n ℂ) * cfc f X * star (U : Matrix n n ℂ) := by
  have hY : ((U : Matrix n n ℂ) * X * star (U : Matrix n n ℂ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.star_eq_conjTranspose, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, hX.eq, Matrix.mul_assoc]
  refine cfc_transfer hX hY (fun Z => (U : Matrix n n ℂ) * Z * star (U : Matrix n n ℂ))
    (fun p => ?_) f
  have h := Polynomial.aeval_algHom_apply
    ((Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) U).toAlgEquiv.toAlgHom) X p
  simpa using h

lemma cfc_sub_equiv {X : Matrix m m ℂ} (hX : X.IsHermitian) (e : n ≃ m) (f : ℝ → ℝ) :
    cfc f (X.submatrix e e) = (cfc f X).submatrix e e :=
  cfc_transfer hX (hX.submatrix e) (fun Z => Z.submatrix e e)
    (fun p => X5AF.aeval_sub_equiv e X p) f

lemma aeval_diag (d : n → ℝ) (p : ℝ[X]) :
    aeval (diagonal (fun i => ((d i : ℝ) : ℂ))) p =
      diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, diagonal_add]
  | monomial k a =>
    simp only [aeval_monomial, diagonal_pow, eval_monomial]
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_mul]
    ext i j
    by_cases h : i = j
    · subst h; simp [Complex.real_smul]
    · simp [h]

lemma diag_herm (d : n → ℝ) : (diagonal (fun i => ((d i : ℝ) : ℂ))).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [diagonal_conjTranspose]; congr 1; ext i; simp [Complex.conj_ofReal]

lemma cfc_diag (d : n → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => ((d i : ℝ) : ℂ))) = diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  set S := (Finset.univ.image d) ∪
    ((diagonal (fun i => ((d i : ℝ) : ℂ))).finite_real_spectrum).toFinset
  rw [cfc_eq_interp (diag_herm d) S ((spec_fin _).trans subset_union_right), aeval_diag]
  congr 1; ext i
  congr 2
  exact Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h)
    (subset_union_left (mem_image_of_mem d (mem_univ i)))

/-! ### relative entropy -/

/-- universe-polymorphic copy of `SimpleSSA.Monotone.relEntropy` -/
noncomputable def relEntropy (ρ σ : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (ρ * cfc Real.log ρ - ρ * cfc Real.log σ)).re

lemma relEnt_def (ρ σ : Matrix n n ℂ) :
    relEntropy ρ σ = (Matrix.trace (ρ * cfc Real.log ρ - ρ * cfc Real.log σ)).re := rfl

lemma relEnt_eq {A : Type} [Fintype A] [DecidableEq A] (ρ σ : Matrix A A ℂ) :
    SimpleSSA.Monotone.relEntropy ρ σ = relEntropy ρ σ := rfl

lemma relEnt_conj (U : unitary (Matrix n n ℂ)) {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) :
    relEntropy ((U : Matrix n n ℂ) * ρ * star (U : Matrix n n ℂ))
      ((U : Matrix n n ℂ) * σ * star (U : Matrix n n ℂ)) = relEntropy ρ σ := by
  rw [relEnt_def, relEnt_def, cfc_conj U hρ, cfc_conj U hσ]
  have hU : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 := Unitary.star_mul_self_of_mem U.2
  congr 1
  set V := (U : Matrix n n ℂ)
  have e : ∀ A B : Matrix n n ℂ, V * A * star V * (V * B * star V) = V * (A * B) * star V := by
    intro A B
    calc V * A * star V * (V * B * star V) = V * A * (star V * V) * B * star V := by
          simp only [Matrix.mul_assoc]
      _ = V * (A * B) * star V := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e, e]
  have h2 : ∀ A B : Matrix n n ℂ, V * A * star V - V * B * star V = V * (A - B) * star V := by
    intro A B; rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

lemma relEnt_sub {ρ σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (e : n ≃ m) :
    relEntropy (ρ.submatrix e e) (σ.submatrix e e) = relEntropy ρ σ := by
  rw [relEnt_def, relEnt_def, cfc_sub_equiv hρ, cfc_sub_equiv hσ, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv]
  have h2 : ∀ A B : Matrix m m ℂ, A.submatrix e e - B.submatrix e e = (A - B).submatrix e e :=
    fun A B => by ext; simp
  rw [h2, X5AF.trace_sub_equiv]

lemma supp_posDef {X : Matrix n n ℂ} (hX : X.PosDef) : supp X = 1 := by
  unfold supp
  rw [← cfc_one ℝ X hX.isHermitian.isSelfAdjoint]
  refine cfc_congr fun x hx => ?_
  obtain ⟨i, rfl⟩ := hX.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
  simp [ind, (hX.eigenvalues_pos i).ne']

lemma relEnt_kron {ρ σ : Matrix m m ℂ} {τ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hτ : τ.PosDef) (htr : τ.trace = 1) :
    relEntropy (ρ ⊗ₖ τ) (σ ⊗ₖ τ) = relEntropy ρ σ := by
  rw [relEnt_def, relEnt_def, log_kron hρ.posSemidef hτ.posSemidef,
    log_kron hσ.posSemidef hτ.posSemidef, supp_posDef hρ, supp_posDef hσ, supp_posDef hτ]
  simp only [Matrix.mul_add, ← mul_kronecker_mul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_add, trace_kronecker, htr, mul_one]
  congr 1; ring

/-! ### full pinching via random signs -/

variable (n) in
abbrev Sg := n → Bool

def sgn (θ : n → Bool) (i : n) : ℂ := if θ i then 1 else -1

lemma sgn_mul_self (θ : n → Bool) (i : n) : sgn θ i * sgn θ i = 1 := by
  unfold sgn; split_ifs <;> norm_num

lemma star_sgn (θ : n → Bool) (i : n) : star (sgn θ i) = sgn θ i := by
  unfold sgn; split_ifs <;> simp

def Cm : Matrix (n × Sg n) (n × Sg n) ℂ := diagonal (fun x => sgn x.2 x.1)

lemma Cm_unitary : (Cm : Matrix (n × Sg n) (n × Sg n) ℂ) ∈ unitary _ := by
  rw [Unitary.mem_iff]
  unfold Cm
  rw [Matrix.star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  constructor
  all_goals
    rw [← diagonal_one]; congr 1; ext x
    simp [star_sgn, sgn_mul_self]

lemma sum_sgn (i j : n) :
    ∑ θ : Sg n, sgn θ i * sgn θ j = if i = j then (Fintype.card (Sg n) : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp [sgn_mul_self]
  · -- flipping the i-th sign is an involution changing the sign of each term
    set φ : Sg n ≃ Sg n :=
      { toFun := fun θ => Function.update θ i (!θ i)
        invFun := fun θ => Function.update θ i (!θ i)
        left_inv := fun θ => by ext k; by_cases hk : k = i <;> simp [Function.update, hk]
        right_inv := fun θ => by ext k; by_cases hk : k = i <;> simp [Function.update, hk] }
    have hs : ∑ θ : Sg n, sgn θ i * sgn θ j = ∑ θ : Sg n, sgn (φ θ) i * sgn (φ θ) j :=
      (Equiv.sum_comp φ _).symm
    have hneg : ∀ θ : Sg n, sgn (φ θ) i * sgn (φ θ) j = -(sgn θ i * sgn θ j) := by
      intro θ
      have h1 : (φ θ) i = !θ i := by simp [φ]
      have h2 : (φ θ) j = θ j := by simp [φ, Function.update, Ne.symm h]
      unfold sgn; rw [h1, h2]; cases θ i <;> cases θ j <;> simp
    rw [Finset.sum_congr rfl (fun θ _ => hneg θ), Finset.sum_neg_distrib] at hs
    have : (2 : ℂ) * ∑ θ : Sg n, sgn θ i * sgn θ j = 0 := by rw [two_mul]; nth_rewrite 2 [hs]; ring
    simpa using this

/-- the uniform mixing state on the sign register -/
noncomputable def tau : Matrix (Sg n) (Sg n) ℂ := ((Fintype.card (Sg n) : ℂ)⁻¹) • 1

lemma tau_posDef : (tau : Matrix (Sg n) (Sg n) ℂ).PosDef := by
  unfold tau
  have hc : (0 : ℝ) < (Fintype.card (Sg n) : ℝ)⁻¹ := by
    have : 0 < Fintype.card (Sg n) := Fintype.card_pos
    positivity
  have := (Matrix.PosDef.one (n := Sg n) (R := ℂ)).smul (a := ((Fintype.card (Sg n) : ℝ)⁻¹ : ℂ))
    (by exact_mod_cast hc)
  simpa using this

lemma tau_trace : (tau : Matrix (Sg n) (Sg n) ℂ).trace = 1 := by
  unfold tau
  rw [trace_smul, trace_one, smul_eq_mul]
  have : (Fintype.card (Sg n) : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_pos).ne'
  field_simp

noncomputable def pin (ρ : Matrix n n ℂ) : Matrix (n × Sg n) (n × Sg n) ℂ :=
  Cm * (ρ ⊗ₖ tau) * star Cm

lemma ptr_pin {n : Type} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) :
    WildeQIT.partialTraceRight (pin ρ) = diagonal (fun i => ρ i i) := by
  ext i j
  simp only [WildeQIT.partialTraceRight, pin, Cm, tau, Matrix.of_apply, Matrix.star_eq_conjTranspose,
    diagonal_conjTranspose, mul_diagonal, diagonal_mul, kroneckerMap_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, Pi.star_apply, star_sgn, smul_eq_mul, mul_one]
  have : ∀ k : Sg n, sgn k i * (ρ i j * (Fintype.card (Sg n) : ℂ)⁻¹) * sgn k j =
      (ρ i j * (Fintype.card (Sg n) : ℂ)⁻¹) * (sgn k i * sgn k j) := fun k => by ring
  rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.mul_sum, sum_sgn]
  have hc : (Fintype.card (Sg n) : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_pos).ne'
  by_cases h : i = j
  · subst h; simp [hc]
  · simp [h]

lemma pin_posDef {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) : (pin ρ).PosDef := by
  have hk : (ρ ⊗ₖ (tau : Matrix (Sg n) (Sg n) ℂ)).PosDef := hρ.kronecker tau_posDef
  have hU : IsUnit (Cm : Matrix (n × Sg n) (n × Sg n) ℂ) := by
    have h := (Unitary.mem_iff.1 (Cm_unitary (n := n))).2
    exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse h)
  unfold pin
  rw [Matrix.star_eq_conjTranspose]
  exact (hk.posSemidef.mul_mul_conjTranspose_same _).posDef_iff_isUnit.mpr
    ((hU.mul hk.isUnit).mul hU.star)

lemma pin_trace {ρ : Matrix n n ℂ} (htr : ρ.trace = 1) : (pin ρ).trace = 1 := by
  have hU : star (Cm : Matrix (n × Sg n) (n × Sg n) ℂ) * Cm = 1 :=
    (Unitary.mem_iff.1 (Cm_unitary (n := n))).1
  unfold pin
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, trace_kronecker, htr, tau_trace, one_mul]

/-- data processing for full pinching (dephasing in the standard basis) -/
theorem dpi_diag {H : Type} [Fintype H] [DecidableEq H] [Nonempty H] {ρ σ : Matrix H H ℂ}
    (hρ : QAlgorithms.IsDensityMatrix ρ) (hρ' : ρ.PosDef)
    (hσ : QAlgorithms.IsDensityMatrix σ) (hσ' : σ.PosDef) :
    relEntropy (diagonal (fun i => ρ i i)) (diagonal (fun i => σ i i)) ≤ relEntropy ρ σ := by
  have h := SimpleSSA.Monotone.eq_4 (pin ρ) (pin σ)
    ⟨(pin_posDef hρ').posSemidef, pin_trace hρ.2⟩ (pin_posDef hρ')
    ⟨(pin_posDef hσ').posSemidef, pin_trace hσ.2⟩ (pin_posDef hσ')
  rw [ptr_pin, ptr_pin, relEnt_eq, relEnt_eq] at h
  refine h.trans (le_of_eq ?_)
  unfold pin
  rw [relEnt_conj ⟨Cm, Cm_unitary⟩ (hρ'.kronecker tau_posDef).isHermitian
    (hσ'.kronecker tau_posDef).isHermitian, relEnt_kron hρ' hσ' tau_posDef tau_trace]

end X5PK
end X5mod_PK_Base

section X5mod_PK_Pinsker
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### classical part -/

lemma logsum (S : Finset ι) (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) :
    (∑ i ∈ S, p i) * Real.log (∑ i ∈ S, p i) - (∑ i ∈ S, p i) * Real.log (∑ i ∈ S, q i) ≤
      ∑ i ∈ S, (p i * Real.log (p i) - p i * Real.log (q i)) := by
  set P := ∑ i ∈ S, p i
  set Q := ∑ i ∈ S, q i
  rcases (Finset.sum_nonneg (fun i (_ : i ∈ S) => hp i)).eq_or_lt with hP | hP
  · have h0 : ∀ i ∈ S, p i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hp i)).1 hP.symm
    have hr : ∑ i ∈ S, (p i * Real.log (p i) - p i * Real.log (q i)) = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [h0 i hi]; simp)
    have hP0 : P = 0 := hP.symm
    rw [hr, hP0]; simp
  have hS : S.Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h; simp [P, h] at hP
  have hQ : 0 < Q := Finset.sum_pos (fun i _ => hq i) hS
  have key : ∀ i ∈ S, p i - q i * P / Q ≤
      (p i * Real.log (p i) - p i * Real.log (q i)) - (p i * Real.log P - p i * Real.log Q) := by
    intro i _
    rcases (hp i).eq_or_lt with h | h
    · rw [← h]; simp; exact div_nonneg (mul_nonneg (hq i).le hP.le) hQ.le
    have hx : 0 < q i * P / (p i * Q) := by have := hq i; positivity
    have hl := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div (by have := hq i; positivity) (by positivity),
      Real.log_mul (hq i).ne' hP.ne', Real.log_mul h.ne' hQ.ne'] at hl
    have e : p i * (q i * P / (p i * Q) - 1) = q i * P / Q - p i := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hl h.le]
  have hsum := Finset.sum_le_sum key
  have e1 : ∑ x ∈ S, q x * P / Q = P := by
    rw [← Finset.sum_div, ← Finset.sum_mul]; exact mul_div_cancel_left₀ P hQ.ne'
  have e2 : ∑ x ∈ S, (p x * Real.log P - p x * Real.log Q) = P * Real.log P - P * Real.log Q := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, e1, e2] at hsum
  linarith

lemma kl_nonneg (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) (hsp : ∑ i, p i = 1)
    (hsq : ∑ i, q i = 1) : 0 ≤ ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) := by
  have := logsum Finset.univ p q hp hq
  rw [hsp, hsq] at this; simpa using this

lemma mlog_div (a b : ℝ) (hb : b ≠ 0) : a * Real.log (a / b) = a * Real.log a - a * Real.log b := by
  rcases eq_or_ne a 0 with h | h
  · subst h; simp
  rw [Real.log_div h hb]; ring

theorem pinsker_cl (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) (hsp : ∑ i, p i = 1)
    (hsq : ∑ i, q i = 1) :
    (∑ i, |p i - q i|) ^ 2 ≤ 2 * ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) := by
  classical
  set A := Finset.univ.filter (fun i => q i ≤ p i)
  set Ac := Finset.univ.filter (fun i => ¬ q i ≤ p i)
  set P := ∑ i ∈ A, p i
  set Q := ∑ i ∈ A, q i
  have hPc : ∑ i ∈ Ac, p i = 1 - P := by
    rw [← hsp, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i)]; ring
  have hQc : ∑ i ∈ Ac, q i = 1 - Q := by
    rw [← hsq, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i)]; ring
  have habs : ∑ i, |p i - q i| = 2 * (P - Q) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => q i ≤ p i)]
    rw [Finset.sum_congr rfl (fun i hi => abs_of_nonneg (sub_nonneg.2 (Finset.mem_filter.1 hi).2)),
      Finset.sum_congr rfl (fun i hi => abs_of_neg (sub_neg.2 (lt_of_not_ge
        (Finset.mem_filter.1 hi).2)))]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
    change (P - Q) + -(∑ i ∈ Ac, p i - ∑ i ∈ Ac, q i) = _
    rw [hPc, hQc]; ring
  have hKL := kl_nonneg p q hp hq hsp hsq
  have hsplit : ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) =
      ∑ i ∈ A, (p i * Real.log (p i) - p i * Real.log (q i)) +
        ∑ i ∈ Ac, (p i * Real.log (p i) - p i * Real.log (q i)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h1 := logsum A p q hp hq
  have h2 := logsum Ac p q hp hq
  rw [hPc, hQc] at h2
  rw [habs]
  have hPQ : Q ≤ P := Finset.sum_le_sum (fun i hi => (Finset.mem_filter.1 hi).2)
  have hP0 : 0 ≤ Q := Finset.sum_nonneg (fun i _ => (hq i).le)
  have hP1 : P ≤ 1 := by
    have : 0 ≤ ∑ i ∈ Ac, p i := Finset.sum_nonneg (fun i _ => hp i)
    linarith
  rcases hP0.eq_or_lt with hQ0 | hQ0
  · -- A is empty
    have hA : A = ∅ := by
      by_contra h
      have := Finset.sum_pos (fun i _ => hq i) (Finset.nonempty_iff_ne_empty.2 h)
      linarith
    have : P = 0 := by simp [P, hA]
    rw [this, ← hQ0]; nlinarith
  rcases (show Q ≤ 1 by linarith).eq_or_lt with hQ1 | hQ1
  · have : P = 1 := by linarith
    rw [this, hQ1]; nlinarith
  have hb := BanditAlgorithm.bernoulli_relative_entropy_pinsker P Q ⟨hQ0.le.trans hPQ, hP1⟩
    ⟨hQ0, hQ1⟩
  unfold BanditAlgorithm.bernoulliRelativeEntropy at hb
  rw [mlog_div _ _ hQ0.ne', mlog_div _ _ (by linarith)] at hb
  nlinarith

/-! ### quantum part -/

lemma relEnt_diag (p q : ι → ℝ) :
    relEntropy (diagonal (fun i => ((p i : ℝ) : ℂ))) (diagonal (fun i => ((q i : ℝ) : ℂ))) =
      ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) := by
  rw [relEnt_def, cfc_diag, cfc_diag, diagonal_mul_diagonal, diagonal_mul_diagonal,
    diagonal_sub, trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.sub_re, Complex.mul_re]

lemma traceNorm_herm {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    QAlgorithms.traceNorm M = ∑ i, |hM.eigenvalues i| := by
  unfold QAlgorithms.traceNorm
  have h1 : Mᴴ * M = cfc (fun x : ℝ => x * x) M := by
    rw [hM.eq, cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) M, cfc_id' ℝ M hM.isSelfAdjoint]
  have h2 : cfc Real.sqrt (Mᴴ * M) = cfc (fun x : ℝ => |x|) M := by
    rw [h1, ← cfc_comp Real.sqrt (fun x : ℝ => x * x) M]
    refine cfc_congr fun x _ => ?_
    simp [Real.sqrt_mul_self_eq_abs]
  rw [h2, X5AF.tr_cfc hM, Complex.re_sum]
  simp

lemma conj_posDef (U : unitary (Matrix ι ι ℂ)) {X : Matrix ι ι ℂ} (hX : X.PosDef) :
    ((U : Matrix ι ι ℂ) * X * star (U : Matrix ι ι ℂ)).PosDef := by
  have hU : IsUnit (U : Matrix ι ι ℂ) :=
    (Matrix.isUnit_iff_isUnit_det _).2
      (Matrix.isUnit_det_of_right_inverse (Unitary.mul_star_self_of_mem U.2))
  rw [Matrix.star_eq_conjTranspose]
  exact (hX.posSemidef.mul_mul_conjTranspose_same _).posDef_iff_isUnit.mpr
    ((hU.mul hX.isUnit).mul hU.star)

lemma conj_trace (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ) * X * star (U : Matrix ι ι ℂ)).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, Unitary.star_mul_self_of_mem U.2, Matrix.one_mul]

/-- quantum Pinsker inequality for invertible states, ground universe -/
theorem pinsker_pd0 {H : Type} [Fintype H] [DecidableEq H] [Nonempty H] {ρ σ : Matrix H H ℂ}
    (hρ : QAlgorithms.IsDensityMatrix ρ) (hρ' : ρ.PosDef)
    (hσ : QAlgorithms.IsDensityMatrix σ) (hσ' : σ.PosDef) :
    QAlgorithms.traceNorm (ρ - σ) ^ 2 ≤ 2 * relEntropy ρ σ := by
  have hM : (ρ - σ).IsHermitian := hρ'.isHermitian.sub hσ'.isHermitian
  set W : unitary (Matrix H H ℂ) := star hM.eigenvectorUnitary
  set ρ' := (W : Matrix H H ℂ) * ρ * star (W : Matrix H H ℂ)
  set σ' := (W : Matrix H H ℂ) * σ * star (W : Matrix H H ℂ)
  have hρ'' : ρ'.PosDef := conj_posDef W hρ'
  have hσ'' : σ'.PosDef := conj_posDef W hσ'
  have hd := dpi_diag (ρ := ρ') (σ := σ') ⟨hρ''.posSemidef, (conj_trace W ρ).trans hρ.2⟩ hρ''
    ⟨hσ''.posSemidef, (conj_trace W σ).trans hσ.2⟩ hσ''
  rw [relEnt_conj W hρ'.isHermitian hσ'.isHermitian] at hd
  set p : H → ℝ := fun i => (ρ' i i).re
  set q : H → ℝ := fun i => (σ' i i).re
  have ep : (diagonal fun i => ρ' i i) = diagonal (fun i => ((p i : ℝ) : ℂ)) := by
    congr 1; ext i; exact (hρ''.isHermitian.coe_re_apply_self i).symm
  have eq' : (diagonal fun i => σ' i i) = diagonal (fun i => ((q i : ℝ) : ℂ)) := by
    congr 1; ext i; exact (hσ''.isHermitian.coe_re_apply_self i).symm
  rw [ep, eq', relEnt_diag] at hd
  have hp : ∀ i, 0 ≤ p i := fun i => by
    have := hρ''.posSemidef.diag_nonneg (i := i)
    exact (Complex.nonneg_iff.1 this).1
  have hq : ∀ i, 0 < q i := fun i => by
    have := hσ''.diag_pos (i := i)
    exact (Complex.pos_iff.1 this).1
  have hsum : ∀ X : Matrix H H ℂ, X.trace = 1 → ∑ i, (X i i).re = 1 := fun X h => by
    rw [← Complex.re_sum]; change (X.trace).re = 1; rw [h]; simp
  have hsp := hsum ρ' ((conj_trace W ρ).trans hρ.2)
  have hsq := hsum σ' ((conj_trace W σ).trans hσ.2)
  have hcl := pinsker_cl p q hp hq hsp hsq
  -- p - q are the eigenvalues of ρ - σ
  have hdiag : ρ' - σ' = diagonal (fun i => ((hM.eigenvalues i : ℝ) : ℂ)) := by
    have hs := hM.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at hs
    simp only [ρ', σ']
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    exact hs
  have hpq : ∀ i, p i - q i = hM.eigenvalues i := fun i => by
    have := congrArg (fun X => (X i i).re) hdiag
    simpa [p, q] using this
  rw [traceNorm_herm hM, ← Finset.sum_congr rfl (fun i _ => congrArg abs (hpq i))]
  linarith

theorem pinsker_pd {H : Type*} [Fintype H] [DecidableEq H] [Nonempty H] {ρ σ : Matrix H H ℂ}
    (hρ : QAlgorithms.IsDensityMatrix ρ) (hρ' : ρ.PosDef)
    (hσ : QAlgorithms.IsDensityMatrix σ) (hσ' : σ.PosDef) :
    QAlgorithms.traceNorm (ρ - σ) ^ 2 ≤ 2 * relEntropy ρ σ := by
  set e : Fin (Fintype.card H) ≃ H := (Fintype.equivFin H).symm
  haveI : Nonempty (Fin (Fintype.card H)) := ⟨⟨0, Fintype.card_pos⟩⟩
  have h := pinsker_pd0 (X5AF.dens_sub hρ e) (hρ'.submatrix e.injective)
    (X5AF.dens_sub hσ e) (hσ'.submatrix e.injective)
  have h2 : ρ.submatrix e e - σ.submatrix e e = (ρ - σ).submatrix e e := by ext; simp
  rw [relEnt_sub hρ'.isHermitian hσ'.isHermitian, h2, X5AF.traceNorm_sub] at h
  exact h

end X5PK
end X5mod_PK_Pinsker

section X5mod_PK_Supp
open Matrix Finset Polynomial Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma aff_eq {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (a b : ℝ) :
    ((a : ℝ) : ℂ) • X + ((b : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) = cfc (fun x : ℝ => a * x + b) X := by
  rw [cfc_add (a := X) (fun x : ℝ => a * x) (fun _ => b), cfc_const_mul a (fun x : ℝ => x) X,
    cfc_id' ℝ X hX.isSelfAdjoint, cfc_const b X hX.isSelfAdjoint, Algebra.algebraMap_eq_smul_one,
    real_smul, real_smul]

lemma cfc_aff {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (a b : ℝ) (f : ℝ → ℝ) :
    cfc f (((a : ℝ) : ℂ) • X + ((b : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) =
      cfc (fun x => f (a * x + b)) X := by
  rw [aff_eq hX a b, ← cfc_comp f (fun x : ℝ => a * x + b) X hX.isSelfAdjoint
    ((X.finite_real_spectrum.image _).continuousOn f)]
  rfl

lemma aff_herm {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (a b : ℝ) :
    (((a : ℝ) : ℂ) • X + ((b : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
  rw [aff_eq hX]; exact (cfc_predicate (R := ℝ) (fun x : ℝ => a * x + b) X : IsSelfAdjoint _)

lemma traceNorm_rsmul (a : ℝ) (ha : 0 ≤ a) (M : Matrix ι ι ℂ) :
    QAlgorithms.traceNorm (((a : ℝ) : ℂ) • M) = a * QAlgorithms.traceNorm M := by
  unfold QAlgorithms.traceNorm
  have hZ : (Mᴴ * M).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have e : (((a : ℝ) : ℂ) • M)ᴴ * (((a : ℝ) : ℂ) • M) = ((a ^ 2 : ℝ) : ℂ) • (Mᴴ * M) := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1; simp [Complex.conj_ofReal]; ring
  rw [e, real_smul, ← cfc_comp_smul (a ^ 2) Real.sqrt (Mᴴ * M) Real.continuous_sqrt.continuousOn hZ.isSelfAdjoint]
  have : cfc (fun x => Real.sqrt (a ^ 2 • x)) (Mᴴ * M) = a • cfc Real.sqrt (Mᴴ * M) := by
    rw [← cfc_smul a Real.sqrt (Mᴴ * M) (X5B2.fin _ _)]
    refine cfc_congr fun x _ => ?_
    simp only [smul_eq_mul]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ha]
  rw [this, trace_smul]
  simp [Complex.real_smul]

/-- the trace term `Re Tr (X log Y)` in the eigenbasis of `Y` -/
lemma tr_mul_cfc {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (f : ℝ → ℝ) :
    (X * cfc f Y).trace.re =
      ∑ j, ((star (hY.eigenvectorUnitary : Matrix ι ι ℂ) * X * hY.eigenvectorUnitary) j j).re *
        f (hY.eigenvalues j) := by
  rw [hY.cfc_eq]
  unfold IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply]
  set U := (hY.eigenvectorUnitary : Matrix ι ι ℂ)
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, ← Matrix.mul_assoc]
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_diagonal, Complex.mul_re]


noncomputable def pert (d ε : ℝ) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (((1 - ε : ℝ)) : ℂ) • X + ((ε / d : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)

end X5PK
end X5mod_PK_Supp

section X5mod_PK_Coh
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Gibbs inequality with support condition -/
lemma kl_nonneg' (p q : n → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hsupp : ∀ i, q i = 0 → p i = 0) (hsp : ∑ i, p i = 1) (hsq : ∑ i, q i = 1) :
    0 ≤ ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) := by
  set q' : n → ℝ := fun i => if q i = 0 then 1 else q i
  have hq' : ∀ i, 0 < q' i := fun i => by
    simp only [q']; split_ifs with h
    · exact one_pos
    · exact lt_of_le_of_ne (hq i) (Ne.symm h)
  set S := Finset.univ.filter (fun i => q i ≠ 0)
  have hpS : ∑ i ∈ S, p i = 1 := by
    rw [← hsp, Finset.sum_filter_of_ne]; intro i _ h; exact fun hq0 => h (hsupp i hq0)
  have hqS : ∑ i ∈ S, q' i = 1 := by
    rw [← hsq, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [q']; split_ifs with h1 h2 <;> simp_all
  have hl := logsum S p q' hp hq'
  rw [hpS, hqS] at hl
  have e : ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) =
      ∑ i ∈ S, (p i * Real.log (p i) - p i * Real.log (q' i)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : q i = 0
    · simp [h, hsupp i h]
    · simp [h, q']
  rw [e]; simpa using hl

end X5PK
end X5mod_PK_Coh

section X5mod_PK_Pin
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

open QAlgorithms.Papers.Independent.Dependency50.P35

variable {I : Type} [Fintype I] [DecidableEq I]

end X5PK
end X5mod_PK_Pin

section X5mod_PK_CohMain
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma ker_single {δ : Matrix n n ℂ} {ρ : Matrix n n ℂ}
    (hker : LinearMap.ker δ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) (hδ : ∀ i j, i ≠ j → δ i j = 0)
    (i : n) (hi : δ i i = 0) : ρ i i = 0 := by
  have hv : Pi.single i (1 : ℂ) ∈ LinearMap.ker δ.mulVecLin := by
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    ext k
    rw [Matrix.mulVec_single_one]
    by_cases h : k = i
    · subst h; simpa using hi
    · simpa using hδ k i h
  have := hker hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
  have h2 := congrFun this i
  rw [Matrix.mulVec_single_one] at h2
  simpa using h2

end X5PK
end X5mod_PK_CohMain

section X5mod_PK_PinMain
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

open QAlgorithms.Papers.Independent.Dependency50.P35

variable {I : Type} [Fintype I] [DecidableEq I]

end X5PK

namespace X5PK
open QAlgorithms.Papers.Independent.Dependency50.P35
variable {I : Type} [Fintype I] [DecidableEq I]

end X5PK
end X5mod_PK_PinMain

section X5mod_PK_CQ
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

variable {L H : Type*} [Fintype L] [DecidableEq L] [Fintype H] [DecidableEq H]

/-- block-diagonal matrix, block index first -/
def bd (X : L → Matrix H H ℂ) : Matrix (L × H) (L × H) ℂ :=
  fun a b => if a.1 = b.1 then X a.1 a.2 b.2 else 0

lemma bd_mul (X Y : L → Matrix H H ℂ) : bd X * bd Y = bd (fun k => X k * Y k) := by
  ext a b
  simp only [bd, Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases h : a.1 = b.1
  · rw [if_pos h, Finset.sum_eq_single a.1]
    · simp [h]
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hk : a.1 = k
    · subst hk; simp [h]
    · simp [hk]

lemma bd_add (X Y : L → Matrix H H ℂ) : bd X + bd Y = bd (fun k => X k + Y k) := by
  ext a b; simp only [bd, Matrix.add_apply]; split_ifs <;> simp

lemma bd_smul (c : ℝ) (X : L → Matrix H H ℂ) : c • bd X = bd (fun k => c • X k) := by
  ext a b; simp only [bd, Matrix.smul_apply]; split_ifs <;> simp

lemma bd_one : bd (fun _ : L => (1 : Matrix H H ℂ)) = 1 := by
  ext a b
  simp only [bd, Matrix.one_apply, Prod.ext_iff]
  by_cases h : a.1 = b.1 <;> simp [h]

lemma bd_pow (X : L → Matrix H H ℂ) (k : ℕ) : bd X ^ k = bd (fun l => X l ^ k) := by
  induction k with
  | zero => simp [bd_one]
  | succ k ih => rw [pow_succ, ih, bd_mul]; simp [pow_succ]

lemma bd_ct (X : L → Matrix H H ℂ) : (bd X)ᴴ = bd (fun k => (X k)ᴴ) := by
  ext a b
  simp only [bd, conjTranspose_apply]
  by_cases h : a.1 = b.1
  · rw [if_pos h.symm, if_pos h, h]
  · rw [if_neg (Ne.symm h), if_neg h]; simp

lemma bd_trace (X : L → Matrix H H ℂ) : (bd X).trace = ∑ k, (X k).trace := by
  simp [Matrix.trace, bd, Fintype.sum_prod_type]

lemma aeval_bd (X : L → Matrix H H ℂ) (p : ℝ[X]) :
    aeval (bd X) p = bd (fun k => aeval (X k) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, bd_add]
  | monomial k a =>
    simp only [aeval_monomial, bd_pow, ← Algebra.smul_def, bd_smul]

lemma bd_herm {X : L → Matrix H H ℂ} (hX : ∀ k, (X k).IsHermitian) : (bd X).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [bd_ct]; congr 1; ext k : 1; exact (hX k).eq

lemma cfc_bd {X : L → Matrix H H ℂ} (hX : ∀ k, (X k).IsHermitian) (f : ℝ → ℝ) :
    cfc f (bd X) = bd (fun k => cfc f (X k)) := by
  set S := ((bd X).finite_real_spectrum).toFinset ∪
    Finset.univ.biUnion (fun k => ((X k).finite_real_spectrum).toFinset)
  rw [cfc_eq_interp (bd_herm hX) S ((spec_fin _).trans subset_union_left), aeval_bd]
  congr 1; ext k : 1
  rw [cfc_eq_interp (hX k) S ((spec_fin _).trans (fun x hx => subset_union_right
    (Finset.mem_biUnion.2 ⟨k, mem_univ k, hx⟩)))]

open QAlgorithms.Papers.Independent.Dependency50.P24

end X5PK

namespace X5PK
open QAlgorithms.Papers.Independent.Dependency50.P24
variable {L H : Type*} [Fintype L] [DecidableEq L] [Fintype H] [DecidableEq H]

end X5PK
end X5mod_PK_CQ

section X5mod_PK_Twist
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma ker_conj' {V M N : Matrix ι ι ℂ} (hV : Vᴴ * V = 1)
    (h : LinearMap.ker M.mulVecLin ≤ LinearMap.ker N.mulVecLin) :
    LinearMap.ker (V * M * Vᴴ).mulVecLin ≤ LinearMap.ker (V * N * Vᴴ).mulVecLin := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have h1 : M *ᵥ (Vᴴ *ᵥ v) = 0 := by
    have := congrArg (fun x => Vᴴ *ᵥ x) hv
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero, ← Matrix.mul_assoc, hV,
      Matrix.one_mul] at this
    simpa [Matrix.mulVec_mulVec] using this
  have h2 := h (show Vᴴ *ᵥ v ∈ LinearMap.ker M.mulVecLin by simpa using h1)
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]

end X5PK

namespace X5PK
variable {J H : Type*} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]

end X5PK
end X5mod_PK_Twist

section X5mod_PK_Pk2
open Matrix Finset Polynomial Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

/-- quantum Pinsker inequality under the support condition `ker σ ⊆ ker ρ` -/
theorem pinsker_ker {H : Type*} [Fintype H] [DecidableEq H] [Nonempty H] {ρ σ : Matrix H H ℂ}
    (hρ : QAlgorithms.IsDensityMatrix ρ) (hσ : QAlgorithms.IsDensityMatrix σ)
    (hker : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) :
    QAlgorithms.traceNorm (ρ - σ) ^ 2 ≤ 2 * relEntropy ρ σ := by
  set d : ℝ := (Fintype.card H : ℝ)
  have hd : 0 < d := by simp only [d]; exact_mod_cast Fintype.card_pos (α := H)
  have hρH := hρ.1.isHermitian
  have hσH := hσ.1.isHermitian
  set U := (hσH.eigenvectorUnitary : Matrix H H ℂ)
  set s := hσH.eigenvalues
  set l := hρH.eigenvalues
  set r : H → ℝ := fun j => ((star U * ρ * U) j j).re
  let F : ℝ → ℝ := fun ε =>
    (∑ i, ((1 - ε) * l i + ε / d) * Real.log ((1 - ε) * l i + ε / d)) -
      ∑ j, ((1 - ε) * r j + ε / d) * Real.log ((1 - ε) * s j + ε / d)
  -- Claim A
  have hA : ∀ ε : ℝ, relEntropy (pert d ε ρ) (pert d ε σ) = F ε := by
    intro ε
    have h1 := aff_herm hρH (1 - ε) (ε / d)
    rw [relEnt_def, Matrix.trace_sub, Complex.sub_re]
    unfold pert
    rw [mul_log _ h1, cfc_aff hρH, cfc_aff hσH, X5AF.tr_cfc hρH, Complex.re_sum,
      tr_mul_cfc h1 hσH]
    simp only [Complex.ofReal_re]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Unitary.star_mul_self_of_mem hσH.eigenvectorUnitary.2]
    simp [r, Complex.mul_re]
    left; rfl
  -- support facts
  have hsd : star U * σ * U = diagonal (fun j => ((s j : ℝ) : ℂ)) := by
    have hs := hσH.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at hs
    simp only [Unitary.coe_star, star_star] at hs
    exact hs
  have hs0 : ∀ j, 0 ≤ s j := fun j => hσ.1.eigenvalues_nonneg j
  have hr0 : ∀ j, 0 ≤ r j := fun j => by
    have h := (hρ.1.conjTranspose_mul_mul_same U).diag_nonneg (i := j)
    rw [← Matrix.star_eq_conjTranspose] at h
    exact (Complex.nonneg_iff.1 h).1
  have hrs : ∀ j, s j = 0 → r j = 0 := fun j hj => by
    have hV : (Uᴴ)ᴴ * Uᴴ = 1 := by
      rw [conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose]
      exact Unitary.mul_star_self_of_mem hσH.eigenvectorUnitary.2
    have hk := ker_conj' hV hker
    rw [conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose, hsd] at hk
    have := ker_single hk (fun a b hab => by simp [hab]) j (by simp [hj])
    simp [r, this]
  -- Claim B: continuity of F at 0
  have hB : ContinuousAt F 0 := by
    have c1 : ∀ i, ContinuousAt (fun ε : ℝ => ((1 - ε) * l i + ε / d) *
        Real.log ((1 - ε) * l i + ε / d)) 0 := fun i =>
      (Real.continuous_mul_log.comp (by fun_prop : Continuous fun ε : ℝ =>
        (1 - ε) * l i + ε / d)).continuousAt
    have c2 : ∀ j, ContinuousAt (fun ε : ℝ => ((1 - ε) * r j + ε / d) *
        Real.log ((1 - ε) * s j + ε / d)) 0 := fun j => by
      rcases (hs0 j).eq_or_lt with h | h
      · have hr := hrs j h.symm
        rw [hr, ← h]
        simp only [mul_zero, zero_add]
        exact (Real.continuous_mul_log.comp (by fun_prop : Continuous fun ε : ℝ =>
          ε / d)).continuousAt
      · refine ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) ?_)
        simp; exact h.ne'
    exact (tendsto_finsetSum _ (fun i _ => c1 i)).sub (tendsto_finsetSum _ (fun j _ => c2 j))
  -- Claim C
  have hC : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ((1 - ε) * QAlgorithms.traceNorm (ρ - σ)) ^ 2 ≤ 2 * F ε := by
    intro ε hε
    have ha : (0 : ℝ) ≤ 1 - ε := by linarith [hε.2]
    have hb : 0 < ε / d := div_pos hε.1 hd
    have hpd : ∀ X : Matrix H H ℂ, QAlgorithms.IsDensityMatrix X →
        QAlgorithms.IsDensityMatrix (pert d ε X) ∧ (pert d ε X).PosDef := by
      intro X hX
      have hp : (pert d ε X).PosDef := by
        unfold pert
        refine Matrix.PosDef.posSemidef_add (hX.1.smul (by exact_mod_cast ha)) ?_
        have := (Matrix.PosDef.one (n := H) (R := ℂ)).smul (a := ((ε / d : ℝ) : ℂ))
          (by exact_mod_cast hb)
        exact this
      refine ⟨⟨hp.posSemidef, ?_⟩, hp⟩
      unfold pert
      rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hX.2, Matrix.trace_one]
      simp only [smul_eq_mul, mul_one]
      push_cast
      field_simp
      simp only [d]; push_cast; ring
    obtain ⟨h1, h2⟩ := hpd ρ hρ
    obtain ⟨h3, h4⟩ := hpd σ hσ
    have hp := pinsker_pd h1 h2 h3 h4
    have e : pert d ε ρ - pert d ε σ = (((1 - ε : ℝ)) : ℂ) • (ρ - σ) := by
      unfold pert; rw [add_sub_add_right_eq_sub, ← smul_sub]
    rw [e, traceNorm_rsmul _ ha, hA] at hp
    exact hp
  -- Claim D
  have hD : F 0 = relEntropy ρ σ := by
    rw [← hA 0]; unfold pert; simp
  -- limit
  have t1 : Tendsto (fun ε : ℝ => ((1 - ε) * QAlgorithms.traceNorm (ρ - σ)) ^ 2) (𝓝[>] 0)
      (𝓝 (QAlgorithms.traceNorm (ρ - σ) ^ 2)) := by
    have : Continuous (fun ε : ℝ => ((1 - ε) * QAlgorithms.traceNorm (ρ - σ)) ^ 2) := by fun_prop
    have h := this.tendsto 0
    simp only [sub_zero, one_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun ε => 2 * F ε) (𝓝[>] 0) (𝓝 (2 * relEntropy ρ σ)) := by
    rw [← hD]; exact (hB.const_mul 2).tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto t1 t2
    (Filter.mem_of_superset (Ioo_mem_nhdsGT one_pos) fun ε hε => hC ε hε)

end X5PK
end X5mod_PK_Pk2

section X5mod_PK_Cop
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
set_option linter.unusedSectionVars false
open QAlgorithms.Papers.Independent.Information100.P60 (copies)

variable {I : Type*} [Fintype I] [DecidableEq I]

end X5PK

namespace X5PK
open QAlgorithms.Papers.Independent.Information100.P60 (copies)
open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy IsSupported)

end X5PK
end X5mod_PK_Cop

section X5mod_PK_Mean
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
open QAlgorithms.Papers.Independent.Dependency50.P24
set_option linter.unusedSectionVars false

variable {L H : Type*} [Fintype L] [DecidableEq L] [Fintype H] [DecidableEq H]

lemma bd_psd {X : L → Matrix H H ℂ} (h : ∀ k, (X k).PosSemidef) : (bd X).PosSemidef := by
  have : ∀ k, ∃ B : Matrix H H ℂ, X k = star B * B := fun k =>
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (h k).nonneg
  choose B hB using this
  have e : bd X = (bd B)ᴴ * bd B := by
    rw [bd_ct, bd_mul]; congr 1; ext k : 1; rw [hB k]; rfl
  rw [e]; exact posSemidef_conjTranspose_mul_self _

end X5PK
end X5mod_PK_Mean

section X5mod_PK_Add
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

section
variable {L H : Type*} [Fintype L] [DecidableEq L] [Fintype H] [DecidableEq H]

lemma bd_sub (X Y : L → Matrix H H ℂ) : bd X - bd Y = bd (fun k => X k - Y k) := by
  ext a b; simp only [bd, Matrix.sub_apply]; split_ifs <;> simp

lemma relEnt_bd {X Y : L → Matrix H H ℂ} (hX : ∀ k, (X k).IsHermitian)
    (hY : ∀ k, (Y k).IsHermitian) :
    relEntropy (bd X) (bd Y) = ∑ k, relEntropy (X k) (Y k) := by
  rw [relEnt_def, cfc_bd hX, cfc_bd hY, bd_mul, bd_mul, bd_sub, bd_trace, Complex.re_sum]
  rfl

/-- `relEnt (s X) (t Y)` for positive definite `X, Y` -/
lemma relEnt_smul {X Y : Matrix H H ℂ} (hX : X.PosDef) (hY : Y.PosDef) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) :
    relEntropy (s • X) (t • Y) =
      s * relEntropy X Y + s * X.trace.re * (Real.log s - Real.log t) := by
  have lg : ∀ {Z : Matrix H H ℂ}, Z.PosDef → ∀ {r : ℝ}, 0 < r →
      cfc Real.log (r • Z) = algebraMap ℝ _ (Real.log r) + cfc Real.log Z := by
    intro Z hZ r hr
    have e1 : r • Z = ((r : ℝ) : ℂ) • Z + ((0 : ℝ) : ℂ) • (1 : Matrix H H ℂ) := by
      simp
    rw [e1, cfc_aff hZ.isHermitian, ← cfc_const_add (Real.log r) Real.log Z
      (hf := Z.finite_real_spectrum.continuousOn _)]
    refine cfc_congr fun x hx => ?_
    obtain ⟨i, rfl⟩ := hZ.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
    simp only [add_zero]
    exact Real.log_mul hr.ne' (hZ.eigenvalues_pos i).ne'
  rw [relEnt_def, relEnt_def, lg hX hs, lg hY ht]
  simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Complex.sub_re,
    Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring
end

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- flag state, flag (`Bool`) on the right -/
noncomputable def flg (X Y : Matrix H H ℂ) : Matrix (H × Bool) (H × Bool) ℂ :=
  (bd (fun b : Bool => if b then X else Y)).submatrix (Equiv.prodComm H Bool) (Equiv.prodComm H Bool)

lemma flg_ptr {H : Type} [Fintype H] [DecidableEq H] (X Y : Matrix H H ℂ) : WildeQIT.partialTraceRight (flg X Y) = X + Y := by
  ext i j
  simp [WildeQIT.partialTraceRight, flg, bd, add_comm]

lemma flg_trace (X Y : Matrix H H ℂ) : (flg X Y).trace = X.trace + Y.trace := by
  rw [flg, X5AF.trace_sub_equiv, bd_trace]; simp [add_comm]

lemma flg_relEnt {X Y Z W : Matrix H H ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hZ : Z.IsHermitian) (hW : W.IsHermitian) :
    relEntropy (flg X Y) (flg Z W) = relEntropy X Z + relEntropy Y W := by
  have h1 : ∀ b : Bool, (if b then X else Y).IsHermitian := fun b => by cases b <;> simpa
  have h2 : ∀ b : Bool, (if b then Z else W).IsHermitian := fun b => by cases b <;> simpa
  rw [flg, flg, relEnt_sub (bd_herm h1) (bd_herm h2), relEnt_bd h1 h2]
  simp [add_comm]

lemma flg_psd {X Y : Matrix H H ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (flg X Y).PosSemidef :=
  (bd_psd (fun b => by cases b <;> simpa)).submatrix _

lemma flg_posDef {X Y : Matrix H H ℂ} (hX : X.PosDef) (hY : Y.PosDef) : (flg X Y).PosDef := by
  refine (flg_psd hX.posSemidef hY.posSemidef).posDef_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (B := flg X⁻¹ Y⁻¹) ?_))
  rw [flg, flg, Matrix.submatrix_mul_equiv, bd_mul]
  have : (fun k : Bool => (if k then X else Y) * (if k then X⁻¹ else Y⁻¹)) = fun _ => 1 := by
    ext k : 1
    cases k
    · exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hY.isUnit)
    · exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hX.isUnit)
  rw [this, bd_one]
  exact Matrix.submatrix_one_equiv _

lemma ptr_smul {a b : Type} [Fintype b] (r : ℝ) (M : Matrix (a × b) (a × b) ℂ) :
    WildeQIT.partialTraceRight (r • M) = r • WildeQIT.partialTraceRight M := by
  ext i j; simp [WildeQIT.partialTraceRight, Finset.smul_sum]

lemma tr_re {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    M.trace = ((M.trace.re : ℝ) : ℂ) := by
  have := (Complex.nonneg_iff.1 hM.trace_nonneg).2
  exact Complex.ext (by simp) (by simp [← this])

/-- joint subadditivity for positive definite arguments -/
lemma joint {H : Type} [Fintype H] [DecidableEq H] [Nonempty H] {A B C D : Matrix H H ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hC : C.PosDef) (hD : D.PosDef) :
    relEntropy (A + C) (B + D) ≤ relEntropy A B + relEntropy C D := by
  have hω := flg_posDef hA hC
  have hτ := flg_posDef hB hD
  set ω := flg A C
  set τ := flg B D
  have pos : ∀ {M : Matrix (H × Bool) (H × Bool) ℂ}, M.PosDef → 0 < M.trace.re := fun hM => by
    have h := hM.trace_pos
    exact (Complex.lt_def.1 h).1
  have dens : ∀ {M : Matrix (H × Bool) (H × Bool) ℂ}, M.PosDef →
      QAlgorithms.IsDensityMatrix ((M.trace.re)⁻¹ • M) ∧ ((M.trace.re)⁻¹ • M).PosDef := by
    intro M hM
    have hp := pos hM
    have hpd : ((M.trace.re)⁻¹ • M).PosDef := hM.smul (inv_pos.2 hp)
    refine ⟨⟨hpd.posSemidef, ?_⟩, hpd⟩
    rw [Matrix.trace_smul, tr_re hM.posSemidef]
    apply Complex.ext <;> simp [hp.ne']
  obtain ⟨d1, d2⟩ := dens hω
  obtain ⟨d3, d4⟩ := dens hτ
  have h := SimpleSSA.Monotone.eq_4 _ _ d1 d2 d3 d4
  rw [relEnt_eq, relEnt_eq, ptr_smul, ptr_smul, flg_ptr, flg_ptr,
    relEnt_smul (hA.add hC) (hB.add hD) (inv_pos.2 (pos hω)) (inv_pos.2 (pos hτ)),
    relEnt_smul hω hτ (inv_pos.2 (pos hω)) (inv_pos.2 (pos hτ)),
    flg_relEnt hA.isHermitian hC.isHermitian hB.isHermitian hD.isHermitian] at h
  have e : (A + C).trace.re = ω.trace.re := by rw [flg_trace, Matrix.trace_add]
  rw [e] at h
  have := inv_pos.2 (pos hω)
  nlinarith

/-- `X + ε` -/
noncomputable def pe (ε : ℝ) (X : Matrix H H ℂ) : Matrix H H ℂ :=
  ((1 : ℝ) : ℂ) • X + ((ε : ℝ) : ℂ) • (1 : Matrix H H ℂ)

lemma pe_posDef {X : Matrix H H ℂ} (hX : X.PosSemidef) {ε : ℝ} (hε : 0 < ε) : (pe ε X).PosDef :=
  Matrix.PosDef.posSemidef_add (by simpa using hX)
    ((Matrix.PosDef.one (n := H) (R := ℂ)).smul (a := ((ε : ℝ) : ℂ)) (by exact_mod_cast hε))

lemma relEnt_self (X : Matrix H H ℂ) : relEntropy X X = 0 := by
  simp [relEnt_def]

/-- continuity of `ε ↦ D(X + cε ‖ Y + cε)` at `0` under the support condition -/
theorem cont {X Y : Matrix H H ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hker : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) (c : ℝ) :
    Tendsto (fun ε => relEntropy (pe (c * ε) X) (pe (c * ε) Y)) (𝓝 0) (𝓝 (relEntropy X Y)) := by
  have hρH := hX.isHermitian
  have hσH := hY.isHermitian
  set U := (hσH.eigenvectorUnitary : Matrix H H ℂ)
  set s := hσH.eigenvalues
  set l := hρH.eigenvalues
  set r : H → ℝ := fun j => ((star U * X * U) j j).re
  let F : ℝ → ℝ := fun ε =>
    (∑ i, (1 * l i + ε) * Real.log (1 * l i + ε)) -
      ∑ j, (1 * r j + ε) * Real.log (1 * s j + ε)
  have hA : ∀ ε : ℝ, relEntropy (pe ε X) (pe ε Y) = F ε := by
    intro ε
    have h1 := aff_herm hρH 1 ε
    rw [relEnt_def, Matrix.trace_sub, Complex.sub_re]
    unfold pe
    rw [mul_log _ h1, cfc_aff hρH, cfc_aff hσH, X5AF.tr_cfc hρH, Complex.re_sum,
      tr_mul_cfc h1 hσH]
    simp only [Complex.ofReal_re]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Unitary.star_mul_self_of_mem hσH.eigenvectorUnitary.2]
    simp [r, Complex.mul_re]
    rfl
  have hsd : star U * Y * U = diagonal (fun j => ((s j : ℝ) : ℂ)) := by
    have hs := hσH.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at hs
    simp only [Unitary.coe_star, star_star] at hs
    exact hs
  have hs0 : ∀ j, 0 ≤ s j := fun j => hY.eigenvalues_nonneg j
  have hrs : ∀ j, s j = 0 → r j = 0 := fun j hj => by
    have hV : (Uᴴ)ᴴ * Uᴴ = 1 := by
      rw [conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose]
      exact Unitary.mul_star_self_of_mem hσH.eigenvectorUnitary.2
    have hk := ker_conj' hV hker
    rw [conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose, hsd] at hk
    have := ker_single hk (fun a b hab => by simp [hab]) j (by simp [hj])
    simp [r, this]
  have hB : ContinuousAt F 0 := by
    have c1 : ∀ i, ContinuousAt (fun ε : ℝ => (1 * l i + ε) *
        Real.log (1 * l i + ε)) 0 := fun i =>
      (Real.continuous_mul_log.comp (by fun_prop : Continuous fun ε : ℝ =>
        1 * l i + ε)).continuousAt
    have c2 : ∀ j, ContinuousAt (fun ε : ℝ => (1 * r j + ε) *
        Real.log (1 * s j + ε)) 0 := fun j => by
      rcases (hs0 j).eq_or_lt with h | h
      · have hr := hrs j h.symm
        rw [hr, ← h]
        simp only [mul_zero, zero_add]
        exact Real.continuous_mul_log.continuousAt
      · refine ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) ?_)
        simp; exact h.ne'
    exact (tendsto_finsetSum _ (fun i _ => c1 i)).sub (tendsto_finsetSum _ (fun j _ => c2 j))
  have hD : F 0 = relEntropy X Y := by
    rw [← hA 0]; unfold pe; simp
  have hc : Tendsto (fun ε : ℝ => c * ε) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_const_mul c).tendsto 0
  have := hB.tendsto.comp hc
  rw [hD] at this
  refine this.congr fun ε => ?_
  simp only [Function.comp, hA]

end X5PK
end X5mod_PK_Add

section X5mod_PR_Main
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PR
open X5QC X5PK
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Re Tr (σ supp τ) = Re Tr σ` when `ker τ ⊆ ker σ` -/
lemma tr_supp {σ τ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (hτ : τ.PosSemidef)
    (hker : LinearMap.ker τ.mulVecLin ≤ LinearMap.ker σ.mulVecLin) :
    (σ * supp τ).trace.re = σ.trace.re := by
  set V := (hτ.1.eigenvectorUnitary : Matrix ι ι ℂ)
  set s := hτ.1.eigenvalues
  set w : ι → ℝ := fun j => ((star V * σ * V) j j).re
  have h1 := tr_mul_cfc hσ.1 hτ.1 ind
  have h2 := tr_mul_cfc hσ.1 hτ.1 (fun _ => 1)
  rw [cfc_const_one ℝ τ, Matrix.mul_one] at h2
  change (σ * supp τ).trace.re = ∑ j, w j * ind (s j) at h1
  change σ.trace.re = ∑ j, w j * 1 at h2
  have hsd : star V * τ * V = diagonal (fun j => ((s j : ℝ) : ℂ)) := by
    have hs := hτ.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at hs
    simp only [Unitary.coe_star, star_star] at hs
    exact hs
  have hsupp : ∀ j, s j = 0 → w j = 0 := fun j hj => by
    have hV : (Vᴴ)ᴴ * Vᴴ = 1 := by
      rw [conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose]
      exact Unitary.mul_star_self_of_mem hτ.1.eigenvectorUnitary.2
    have hk := ker_conj' hV hker
    rw [conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose, hsd] at hk
    have := ker_single hk (fun a b hab => by simp [hab]) j (by simp [hj])
    simp [w, this]
  rw [h1, h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : s j = 0
  · simp [hsupp j hj]
  · simp [ind, hj]

/-- `Re Tr (σ log (c τ)) = log c · Re Tr σ + Re Tr (σ log τ)` when `ker τ ⊆ ker σ` -/
lemma tr_log_smul {σ τ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (hτ : τ.PosSemidef)
    (hker : LinearMap.ker τ.mulVecLin ≤ LinearMap.ker σ.mulVecLin) {c : ℝ} (hc : 0 < c) :
    (σ * cfc Real.log ((c : ℂ) • τ)).trace.re =
      Real.log c * σ.trace.re + (σ * cfc Real.log τ).trace.re := by
  rw [cfc_log_smul hc τ hτ.1, Matrix.mul_add, Matrix.trace_add, Complex.add_re, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, tr_supp hσ hτ hker]

section
variable {L H : Type*} [Fintype L] [DecidableEq L] [Fintype H] [DecidableEq H]

end

section priv
open QAlgorithms.Papers.Independent.Dependency50.P24
variable {d : ℕ} [NeZero d] {H : Type*} [Fintype H] [DecidableEq H]

end priv

section sep
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

end sep

section final
open QAlgorithms.Papers.Independent.Dependency50.P24
variable {d : ℕ} [NeZero d] {S T' : Type*} [Fintype S] [Fintype T'] [DecidableEq S] [DecidableEq T']

end final

section bits
open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma relEnt_nonneg [Nonempty I] {ρ σ : Matrix I I ℂ} (hρ : QAlgorithms.IsDensityMatrix ρ)
    (hσ : QAlgorithms.IsDensityMatrix σ)
    (hker : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) : 0 ≤ X5PK.relEntropy ρ σ := by
  have := pinsker_ker hρ hσ hker
  nlinarith [sq_nonneg (QAlgorithms.traceNorm (ρ - σ))]

end bits

end X5PR
end X5mod_PR_Main

section X5mod_PN_Pin
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PN
open X5QC X5PK
set_option linter.unusedSectionVars false

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- a complete family of orthogonal projections -/
structure PF (Q : K → Matrix H H ℂ) : Prop where
  herm : ∀ k, (Q k)ᴴ = Q k
  idem : ∀ k, Q k * Q k = Q k
  orth : ∀ k l, k ≠ l → Q k * Q l = 0
  compl : ∑ k, Q k = 1

/-- pinching -/
noncomputable def pinQ (Q : K → Matrix H H ℂ) (X : Matrix H H ℂ) : Matrix H H ℂ := ∑ k, Q k * X * Q k

variable {Q : K → Matrix H H ℂ}

lemma mul_pin (hQ : PF Q) (k : K) (X : Matrix H H ℂ) : Q k * pinQ Q X = Q k * X * Q k := by
  unfold pinQ; rw [Finset.mul_sum, Finset.sum_eq_single k]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ.idem]
  · intro l _ hl; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ.orth k l (Ne.symm hl)]; simp
  · simp

lemma pin_mul (hQ : PF Q) (k : K) (X : Matrix H H ℂ) : pinQ Q X * Q k = Q k * X * Q k := by
  unfold pinQ; rw [Finset.sum_mul, Finset.sum_eq_single k]
  · rw [Matrix.mul_assoc _ (Q k), hQ.idem]
  · intro l _ hl; rw [Matrix.mul_assoc _ (Q l), hQ.orth l k hl]; simp
  · simp

lemma comm_pin (hQ : PF Q) (k : K) (X : Matrix H H ℂ) : Commute (Q k) (pinQ Q X) := by
  show Q k * pinQ Q X = pinQ Q X * Q k
  rw [mul_pin hQ, pin_mul hQ]

lemma tr_pin (hQ : PF Q) (X M : Matrix H H ℂ) (hM : ∀ k, Commute (Q k) M) :
    (pinQ Q X * M).trace = (X * M).trace := by
  have e : ∀ k, (Q k * X * Q k * M).trace = (X * M * Q k).trace := fun k => by
    rw [show Q k * X * Q k * M = Q k * (X * Q k * M) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, Matrix.mul_assoc X, (hM k).eq, Matrix.mul_assoc, Matrix.mul_assoc, hQ.idem,
      ← Matrix.mul_assoc]
  rw [pinQ, Finset.sum_mul, Matrix.trace_sum]
  simp only [e]
  rw [← Matrix.trace_sum, ← Finset.mul_sum, hQ.compl, Matrix.mul_one]

lemma pin_psd (hQ : PF Q) {X : Matrix H H ℂ} (hX : X.PosSemidef) : (pinQ Q X).PosSemidef := by
  unfold pinQ
  refine Matrix.posSemidef_sum _ fun k _ => ?_
  have := hX.conjTranspose_mul_mul_same (Q k)
  rwa [hQ.herm] at this

lemma pinQ_trace (hQ : PF Q) (X : Matrix H H ℂ) : (pinQ Q X).trace = X.trace := by
  have := tr_pin hQ X 1 (fun k => Commute.one_right _)
  simpa using this

/-- vectors in the kernel of a pinched PSD matrix -/
lemma ker_aux (hQ : PF Q) {σ : Matrix H H ℂ} (hσ : σ.PosSemidef) {v : H → ℂ}
    (hv : pinQ Q σ *ᵥ v = 0) (k : K) : σ *ᵥ (Q k *ᵥ v) = 0 := by
  have e : ∀ l, star v ⬝ᵥ ((Q l * σ * Q l) *ᵥ v) = star (Q l *ᵥ v) ⬝ᵥ (σ *ᵥ (Q l *ᵥ v)) := by
    intro l
    rw [Matrix.star_mulVec, hQ.herm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec]
  have h0 : ∑ l, star (Q l *ᵥ v) ⬝ᵥ (σ *ᵥ (Q l *ᵥ v)) = 0 := by
    simp only [← e]
    rw [← dotProduct_sum, ← Matrix.sum_mulVec]
    rw [show (∑ l, Q l * σ * Q l) = pinQ Q σ from rfl, hv, dotProduct_zero]
  have hn : ∀ l ∈ Finset.univ, 0 ≤ star (Q l *ᵥ v) ⬝ᵥ (σ *ᵥ (Q l *ᵥ v)) :=
    fun l _ => hσ.dotProduct_mulVec_nonneg _
  have := (Finset.sum_eq_zero_iff_of_nonneg hn).1 h0 k (Finset.mem_univ _)
  exact (hσ.dotProduct_mulVec_zero_iff _).1 this

lemma ker_pin (hQ : PF Q) {ω σ : Matrix H H ℂ} (hσ : σ.PosSemidef)
    (hker : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ω.mulVecLin) :
    LinearMap.ker (pinQ Q σ).mulVecLin ≤ LinearMap.ker (pinQ Q ω).mulVecLin := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have h : ∀ k, ω *ᵥ (Q k *ᵥ v) = 0 := fun k => by
    have := hker (show Q k *ᵥ v ∈ LinearMap.ker σ.mulVecLin by simpa using ker_aux hQ hσ hv k)
    simpa using this
  unfold pinQ
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

lemma ker_pin_self (hQ : PF Q) {ρ : Matrix H H ℂ} (hρ : ρ.PosSemidef) :
    LinearMap.ker (pinQ Q ρ).mulVecLin ≤ LinearMap.ker ρ.mulVecLin := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have : v = ∑ k, Q k *ᵥ v := by rw [← Matrix.sum_mulVec, hQ.compl, Matrix.one_mulVec]
  rw [this, Matrix.mulVec_sum]
  exact Finset.sum_eq_zero fun k _ => ker_aux hQ hρ hv k

end X5PN
end X5mod_PN_Pin

section X5mod_PN_Dpi
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PN
open X5QC X5PK
set_option linter.unusedSectionVars false

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- joint subadditivity, universe polymorphic -/
lemma jointT [Nonempty H] {A B C D : Matrix H H ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hC : C.PosDef) (hD : D.PosDef) :
    relEntropy (A + C) (B + D) ≤ relEntropy A B + relEntropy C D := by
  set e := (Fintype.equivFin H).symm
  haveI : NeZero (Fintype.card H) := ⟨Fintype.card_ne_zero⟩
  have h := joint (hA.submatrix e.injective) (hB.submatrix e.injective)
    (hC.submatrix e.injective) (hD.submatrix e.injective)
  have sa : ∀ M N : Matrix H H ℂ, M.submatrix e e + N.submatrix e e = (M + N).submatrix e e :=
    fun M N => by ext; simp
  rwa [sa, sa,
    relEnt_sub (hA.add hC).isHermitian (hB.add hD).isHermitian e,
    relEnt_sub hA.isHermitian hB.isHermitian e, relEnt_sub hC.isHermitian hD.isHermitian e] at h

variable {Q : K → Matrix H H ℂ}

end X5PN
end X5mod_PN_Dpi

section X5mod_PN_Ent
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PN
open X5QC X5PK X5AF
set_option linter.unusedSectionVars false

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {Q : K → Matrix H H ℂ}

lemma T_pin_eq (hQ : PF Q) {ρ : Matrix H H ℂ} (hρ : ρ.PosSemidef) :
    relEntropy ρ (pinQ Q ρ) = T ρ - T (pinQ Q ρ) := by
  have hc : ∀ k, Commute (Q k) (cfc Real.log (pinQ Q ρ)) := fun k =>
    ((comm_pin hQ k ρ).symm.cfc_real Real.log).symm
  rw [relEnt_def, Matrix.trace_sub, Complex.sub_re, ← tr_pin hQ ρ _ hc, mul_log _ hρ.1,
    mul_log _ (pin_psd hQ hρ).1]
  rfl

end X5PN
end X5mod_PN_Ent

section X5mod_PN_Main
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker ENNReal

namespace X5PN
open X5QC X5PK QAlgorithms.Papers.Independent.Information100.P54
set_option linter.unusedSectionVars false

section gen
variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {Q : K → Matrix H H ℂ}

lemma relEnt_split (hQ : PF Q) (ρ τ : Matrix H H ℂ) :
    relEntropy ρ (pinQ Q τ) = relEntropy ρ (pinQ Q ρ) + relEntropy (pinQ Q ρ) (pinQ Q τ) := by
  have hc : ∀ X : Matrix H H ℂ, ∀ k, Commute (Q k) (cfc Real.log (pinQ Q X)) := fun X k =>
    ((comm_pin hQ k X).symm.cfc_real _).symm
  simp only [relEnt_def, Matrix.trace_sub, Complex.sub_re]
  rw [← tr_pin hQ ρ _ (hc τ), ← tr_pin hQ ρ _ (hc ρ)]
  ring
end gen

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J]
  [DecidableEq K]

end X5PN
end X5mod_PN_Main

section X5mod_RA_Dpi
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5RA
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23 X5RB X5PK X5QC
set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

def eU' (I : Type*) : I ≃ Unit × I := (Equiv.punitProd I).symm

lemma tj_eq' (ρ : Matrix I I ℂ) : trivialJoint ρ = reindex (eU' I) (eU' I) ρ := by
  ext x y; simp [trivialJoint, reindex_apply, eU']

lemma itr_eq' (σ : Matrix I I ℂ) :
    identityTensorReference (A := Unit) σ = reindex (eU' I) (eU' I) σ := by
  ext x y; simp [identityTensorReference, reindex_apply, eU', Matrix.kronecker]

lemma logb_cfc' (σ : Matrix I I ℂ) :
    cfc (fun x : ℝ => Real.logb 2 x) σ = (Real.log 2)⁻¹ • cfc Real.log σ := by
  rw [show (fun x : ℝ => Real.logb 2 x) = fun x => (Real.log 2)⁻¹ * Real.log x by
    ext x; simp [Real.logb, div_eq_inv_mul]]
  exact cfc_const_mul _ _ _ (σ.finite_real_spectrum.continuousOn _)

lemma xlogb_cfc' (σ : Matrix I I ℂ) :
    cfc (fun x : ℝ => x * Real.logb 2 x) σ = (Real.log 2)⁻¹ • cfc (fun x : ℝ => x * Real.log x) σ := by
  rw [show (fun x : ℝ => x * Real.logb 2 x) = fun x => (Real.log 2)⁻¹ * (x * Real.log x) by
    ext x; simp [Real.logb]; ring]
  exact cfc_const_mul _ _ _ (σ.finite_real_spectrum.continuousOn _)

lemma fvn_rel {ρ σ : Matrix I I ℂ} (hρ : ρ.IsHermitian) (h : supportedBy ρ σ) :
    fixedVonNeumann (trivialJoint ρ) σ = ((-(relEntropy ρ σ / Real.log 2) : ℝ) : EReal) := by
  unfold fixedVonNeumann
  rw [tj_eq', itr_eq', if_pos ((supp_rx _ _ _).2 h), EReal.coe_eq_coe_iff]
  unfold vnEntropy
  rw [cfc_rx, cfc_rx, rmul, tr_rx, tr_rx, logb_cfc', xlogb_cfc', relEnt_def, mul_log _ hρ]
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_sub]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.sub_re, Complex.smul_re, smul_eq_mul]
  have : Real.log 2 ≠ 0 := by positivity
  field_simp
  ring

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

lemma ker_chan {m : ℕ} (K : Fin m → Matrix κ I ℂ) {ρ σ : Matrix I I ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (hker : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) :
    LinearMap.ker (X5DP.Φ K σ).mulVecLin ≤ LinearMap.ker (X5DP.Φ K ρ).mulVecLin :=
  X5DP.Φ_supp K hρ hσ hker

/-- data processing inequality for the Umegaki relative entropy under any Kraus channel -/
theorem chan_dpi [Nonempty I] [Nonempty κ] {m : ℕ} (K : Fin m → Matrix κ I ℂ)
    (hK : ∑ j, (K j)ᴴ * K j = 1) {ρ σ : Matrix I I ℂ} (hρ : IsDensityMatrix ρ)
    (hσ : IsDensityMatrix σ) (hker : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) :
    relEntropy (X5DP.Φ K ρ) (X5DP.Φ K σ) ≤ relEntropy ρ σ := by
  set E : Superop I κ := krausApply K
  have hE : IsChannel E := ⟨m, K, hK, fun _ => rfl⟩
  have hT : IsDensityMatrix (trivialJoint ρ) := by
    rw [tj_eq']; exact ⟨(psd_rx _ _).2 hρ.1, by rw [tr_rx]; exact hρ.2⟩
  have h := X5DP.fa_one (A := Unit) (trivialJoint ρ) σ hT hσ E hE
  have hid : idTensorSuperop (R := Unit) E (trivialJoint ρ) = trivialJoint (E ρ) := by
    ext p q
    simp only [idTensorSuperop, trivialJoint, Matrix.of_apply]
    rfl
  have eE : ∀ X, E X = X5DP.Φ K X := fun _ => rfl
  rw [hid, eE, eE, fvn_rel hρ.1.isHermitian hker,
    fvn_rel (X5DP.Φ_psd K hρ.1).isHermitian (ker_chan K hρ.1 hσ.1 hker)] at h
  have hl := Real.log_pos one_lt_two
  have h' := EReal.coe_le_coe_iff.1 h
  have : relEntropy (X5DP.Φ K ρ) (X5DP.Φ K σ) / Real.log 2 ≤ relEntropy ρ σ / Real.log 2 := by
    linarith
  exact (div_le_div_iff_of_pos_right hl).1 this

end X5RA
end X5mod_RA_Dpi

section X5mod_RA_Coh
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5RA
open QAlgorithms X5PK X5QC X5PN QAlgorithms.Papers.Independent.Independent1.P04
set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {d : ℕ}

/-- basis projectors -/
def Qd (d : ℕ) (i : Fin d) : CoherenceMatrix d := Matrix.diagonal fun j => if j = i then 1 else 0

lemma PF_Qd : PF (Qd d) where
  herm i := by
    rw [Qd, Matrix.diagonal_conjTranspose]; congr 1; ext j; split_ifs <;> simp_all
  idem i := by
    rw [Qd, Matrix.diagonal_mul_diagonal]; congr 1; ext j; split_ifs <;> simp
  orth i l h := by
    rw [Qd, Qd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]; congr 1; ext j
    split_ifs with h1 h2 <;> simp_all
  compl := by
    ext a b
    simp only [Qd, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h
    · subst h; simp
    · simp

lemma pin_Qd (X : CoherenceMatrix d) : pinQ (Qd d) X = dephasedMatrix X := by
  ext a b
  simp only [pinQ, Qd, Matrix.sum_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, dephasedMatrix,
    Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h; simp
  · simp only [h, if_false]
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs <;> simp_all

lemma deph_diag {X : CoherenceMatrix d} (hX : BasisDiagonal X) : dephasedMatrix X = X := by
  ext a b
  simp only [dephasedMatrix, Matrix.diagonal_apply]
  split_ifs with h
  · rw [h]
  · rw [hX a b h]

lemma deph_basis (X : CoherenceMatrix d) : BasisDiagonal (dephasedMatrix X) := by
  intro i j h; simp [dephasedMatrix, Matrix.diagonal_apply, h]

lemma deph_dens {ρ : CoherenceMatrix d} (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (dephasedMatrix ρ) := by
  rw [← pin_Qd]; exact ⟨pin_psd PF_Qd hρ.1, by rw [pinQ_trace PF_Qd, hρ.2]⟩

lemma ker_deph {ρ : CoherenceMatrix d} (hρ : ρ.PosSemidef) :
    LinearMap.ker (dephasedMatrix ρ).mulVecLin ≤ LinearMap.ker ρ.mulVecLin := by
  rw [← pin_Qd]; exact ker_pin_self PF_Qd hρ

lemma ec_eq {ρ : CoherenceMatrix d} (hρ : ρ.PosSemidef) :
    entropyCoherence d ρ = relEntropy ρ (dephasedMatrix ρ) := by
  unfold entropyCoherence naturalEntropy
  rw [vn_eq, vn_eq, ← pin_Qd, T_pin_eq PF_Qd hρ]
  have : Real.log 2 ≠ 0 := by positivity
  field_simp
  ring

lemma ec_nonneg (hd : 0 < d) {ρ : CoherenceMatrix d} (hρ : IsDensityMatrix ρ) :
    0 ≤ entropyCoherence d ρ := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [ec_eq hρ.1]
  exact X5PR.relEnt_nonneg hρ (deph_dens hρ) (ker_deph hρ.1)

lemma herm_zero {M : CoherenceMatrix d} (hM : M.IsHermitian) (h : QAlgorithms.traceNorm M = 0) :
    M = 0 := by
  rw [traceNorm_herm hM] at h
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (hM.eigenvalues i))).1 h
  rw [← hM.eigenvalues_eq_zero_iff]
  ext i; simpa using h0 i (Finset.mem_univ _)

lemma ec_faithful (hd : 0 < d) {ρ : CoherenceMatrix d} (hρ : IsDensityMatrix ρ) :
    entropyCoherence d ρ = 0 ↔ IncoherentState ρ := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [ec_eq hρ.1]
  constructor
  · intro h
    have hp := pinsker_ker hρ (deph_dens hρ) (ker_deph hρ.1)
    rw [h, mul_zero] at hp
    have h0 : QAlgorithms.traceNorm (ρ - dephasedMatrix ρ) = 0 := by
      have := sq_nonneg (QAlgorithms.traceNorm (ρ - dephasedMatrix ρ))
      nlinarith [sq_eq_zero_iff (a := QAlgorithms.traceNorm (ρ - dephasedMatrix ρ))]
    have hz := herm_zero (hρ.1.isHermitian.sub (deph_dens hρ).1.isHermitian) h0
    have he : ρ = dephasedMatrix ρ := sub_eq_zero.1 hz
    refine ⟨hρ, ?_⟩
    rw [he]; exact deph_basis ρ
  · intro h
    rw [deph_diag h.2]; exact relEnt_self ρ

/-- the relative entropy of coherence is the minimal distance to diagonal states -/
lemma ec_min {τ δ : CoherenceMatrix d} [Nonempty (Fin d)] (hτ : IsDensityMatrix τ)
    (hδ : IsDensityMatrix δ) (hδd : BasisDiagonal δ)
    (hker : LinearMap.ker δ.mulVecLin ≤ LinearMap.ker τ.mulVecLin) :
    relEntropy τ (dephasedMatrix τ) ≤ relEntropy τ δ := by
  have hs := relEnt_split PF_Qd τ δ
  have hk := ker_pin PF_Qd hδ.1 hker
  rw [pin_Qd, pin_Qd, deph_diag hδd] at hs hk
  rw [hs]
  have := X5PR.relEnt_nonneg (deph_dens hτ) hδ hk
  linarith

lemma Φ_diag {e a : ℕ} (K : Fin a → Matrix (Fin e) (Fin d) ℂ)
    (hK : ∀ i, PreservesDiagonalBranch (K i)) {X : CoherenceMatrix d} (hX : X.PosSemidef)
    (hXd : BasisDiagonal X) : BasisDiagonal (X5DP.Φ K X) := by
  intro i j hij
  simp only [X5DP.Φ, Matrix.sum_apply]
  exact Finset.sum_eq_zero fun l _ => hK l X hX hXd i j hij

theorem ec_mono : CoherenceMonotone entropyCoherence := by
  intro d e hd he a K hK ρ hρ
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  haveI : Nonempty (Fin e) := ⟨⟨0, he⟩⟩
  have hτ : IsDensityMatrix (X5DP.Φ K ρ) :=
    ⟨X5DP.Φ_psd K hρ.1, by rw [X5DP.Φ_tr K hK.1, hρ.2]⟩
  have hΔ := deph_dens hρ
  have hδ : IsDensityMatrix (X5DP.Φ K (dephasedMatrix ρ)) :=
    ⟨X5DP.Φ_psd K hΔ.1, by rw [X5DP.Φ_tr K hK.1, hΔ.2]⟩
  have hδd := Φ_diag K hK.2 hΔ.1 (deph_basis ρ)
  have hk := ker_chan K hρ.1 hΔ.1 (ker_deph hρ.1)
  show entropyCoherence e (X5DP.Φ K ρ) ≤ entropyCoherence d ρ
  rw [ec_eq hτ.1, ec_eq hρ.1]
  exact (ec_min hτ hδ hδd hk).trans (chan_dpi K hK.1 hρ hΔ (ker_deph hρ.1))

end X5RA
end X5mod_RA_Coh

section X5mod_RA_Conv
open Matrix Finset Filter Topology
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5RA
open QAlgorithms X5PK X5QC X5PN QAlgorithms.Papers.Independent.Independent1.P04
set_option linter.unusedSectionVars false

section gen
variable {H ι : Type*} [Fintype H] [DecidableEq H]

/-- n-term joint subadditivity, positive definite case -/
lemma sub_pd [Nonempty H] (A B : ι → Matrix H H ℂ) (s : Finset ι) (hs : s.Nonempty)
    (hA : ∀ i ∈ s, (A i).PosDef) (hB : ∀ i ∈ s, (B i).PosDef) :
    (∑ i ∈ s, A i).PosDef ∧ (∑ i ∈ s, B i).PosDef ∧
      relEntropy (∑ i ∈ s, A i) (∑ i ∈ s, B i) ≤ ∑ i ∈ s, relEntropy (A i) (B i) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp only [Finset.sum_singleton]; exact ⟨hA a (by simp), hB a (by simp), le_rfl⟩
  | cons a s ha hs ih =>
    have hA' : ∀ i ∈ s, (A i).PosDef := fun i hi => hA i (Finset.mem_cons_of_mem hi)
    have hB' : ∀ i ∈ s, (B i).PosDef := fun i hi => hB i (Finset.mem_cons_of_mem hi)
    obtain ⟨i1, i2, i3⟩ := ih hA' hB'
    have ha1 := hA a (Finset.mem_cons_self a s)
    have hb1 := hB a (Finset.mem_cons_self a s)
    simp only [Finset.sum_cons]
    exact ⟨ha1.add i1, hb1.add i2, (jointT ha1 hb1 i1 i2).trans (by linarith)⟩

lemma relEnt_scale [Nonempty H] {X Y : Matrix H H ℂ} (hX : X.PosDef) (hY : Y.PosDef) {s : ℝ}
    (hs : 0 < s) : relEntropy (s • X) (s • Y) = s * relEntropy X Y := by
  rw [relEnt_smul hX hY hs hs]; ring

/-- joint convexity of the relative entropy -/
theorem jconv [Nonempty H] {a : ℕ} (p : Fin a → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (ρ σ : Fin a → Matrix H H ℂ) (hρ : ∀ i, (ρ i).PosSemidef) (hσ : ∀ i, (σ i).PosSemidef)
    (hker : ∀ i, LinearMap.ker (σ i).mulVecLin ≤ LinearMap.ker (ρ i).mulVecLin) :
    relEntropy (∑ i, p i • ρ i) (∑ i, p i • σ i) ≤ ∑ i, p i * relEntropy (ρ i) (σ i) := by
  set s := Finset.univ.filter (fun i => p i ≠ 0)
  have hsum : ∀ f : Fin a → ℝ, (∀ i, p i = 0 → f i = 0) → ∑ i ∈ s, f i = ∑ i, f i := by
    intro f hf
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · exact (hf i (not_not.1 h)).symm
  have hsumM : ∀ f : Fin a → Matrix H H ℂ, (∀ i, p i = 0 → f i = 0) → ∑ i ∈ s, f i = ∑ i, f i := by
    intro f hf
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · exact (hf i (not_not.1 h)).symm
  have hs : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := hsum p (fun i h => h)
    rw [h, Finset.sum_empty, hp1] at this
    exact zero_ne_one this
  have hpos : ∀ i ∈ s, 0 < p i := fun i hi =>
    lt_of_le_of_ne (hp0 i) (Ne.symm (Finset.mem_filter.1 hi).2)
  have hps : ∑ i ∈ s, p i = 1 := (hsum p (fun i h => h)).trans hp1
  -- mixtures and their kernels
  have mixpsd : ∀ X : Fin a → Matrix H H ℂ, (∀ i, (X i).PosSemidef) →
      (∑ i, p i • X i).PosSemidef := fun X hX =>
    Matrix.posSemidef_sum _ fun i _ => (hX i).smul (hp0 i)
  have hkm : LinearMap.ker (∑ i, p i • σ i).mulVecLin ≤ LinearMap.ker (∑ i, p i • ρ i).mulVecLin := by
    intro v hv
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    have h0 : ∑ i, p i • (star v ⬝ᵥ σ i *ᵥ v) = 0 := by
      have : star v ⬝ᵥ (∑ i, p i • σ i) *ᵥ v = 0 := by rw [hv, dotProduct_zero]
      rw [Matrix.sum_mulVec, dotProduct_sum] at this
      simpa only [Matrix.smul_mulVec, dotProduct_smul] using this
    have hn : ∀ i ∈ Finset.univ, 0 ≤ p i • (star v ⬝ᵥ σ i *ᵥ v) := fun i _ =>
      smul_nonneg (hp0 i) ((hσ i).dotProduct_mulVec_nonneg v)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).1 h0
    rw [Matrix.sum_mulVec]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hpi : p i = 0
    · simp [hpi]
    · have h1 := hz i (Finset.mem_univ _)
      rw [smul_eq_zero] at h1
      have h2 := h1.resolve_left hpi
      have h3 := (hσ i).dotProduct_mulVec_zero_iff v |>.1 h2
      have h4 := hker i (show v ∈ LinearMap.ker (σ i).mulVecLin by simpa using h3)
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h4
      rw [Matrix.smul_mulVec, h4, smul_zero]
  have t1 := cont (mixpsd ρ hρ) (mixpsd σ hσ) hkm 1
  have t2 : Tendsto (fun ε => ∑ i ∈ s, p i * relEntropy (pe (1 * ε) (ρ i)) (pe (1 * ε) (σ i)))
      (𝓝 0) (𝓝 (∑ i ∈ s, p i * relEntropy (ρ i) (σ i))) :=
    tendsto_finset_sum _ fun i _ => (cont (hρ i) (hσ i) (hker i) 1).const_mul (p i)
  rw [← hsum (fun i => p i * relEntropy (ρ i) (σ i)) (fun i h => by simp [h])]
  refine le_of_tendsto_of_tendsto (t1.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
    (t2.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))) ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hε' : 0 < 1 * ε := by linarith
  have mixpe : ∀ X : Fin a → Matrix H H ℂ,
      ∑ i ∈ s, p i • pe (1 * ε) (X i) = pe (1 * ε) (∑ i, p i • X i) := by
    intro X
    unfold pe
    simp only [Complex.ofReal_one, one_smul, smul_add, Finset.sum_add_distrib]
    rw [hsumM (fun i => p i • X i) (fun i h => by simp [h]), ← Finset.sum_smul, hps, one_smul]
  have key := (sub_pd (fun i => p i • pe (1 * ε) (ρ i)) (fun i => p i • pe (1 * ε) (σ i)) s hs
    (fun i hi => (pe_posDef (hρ i) hε').smul (hpos i hi))
    (fun i hi => (pe_posDef (hσ i) hε').smul (hpos i hi))).2.2
  rw [mixpe, mixpe] at key
  refine key.trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_))
  exact relEnt_scale (pe_posDef (hρ i) hε') (pe_posDef (hσ i) hε') (hpos i hi)
end gen

theorem ec_convex : CoherenceConvex entropyCoherence := by
  intro d hd a p ρ hp hρ
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hc : ∀ X : Fin a → CoherenceMatrix d, ensembleMixture p X = ∑ i, p i • X i := fun X => by
    unfold ensembleMixture
    exact Finset.sum_congr rfl fun i _ => Complex.coe_smul _ _
  have hpsd : (ensembleMixture p ρ).PosSemidef := by
    rw [hc]; exact Matrix.posSemidef_sum _ fun i _ => (hρ i).1.smul (hp.1 i)
  have hdeph : dephasedMatrix (ensembleMixture p ρ) = ∑ i, p i • dephasedMatrix (ρ i) := by
    rw [hc]; ext x y
    simp [dephasedMatrix, Matrix.sum_apply, Matrix.diagonal_apply]
  rw [ec_eq hpsd, hdeph, hc]
  have := jconv p hp.1 hp.2 ρ (fun i => dephasedMatrix (ρ i)) (fun i => (hρ i).1)
    (fun i => (deph_dens (hρ i)).1) (fun i => ker_deph (hρ i).1)
  refine this.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [ec_eq (hρ i).1]

end X5RA
end X5mod_RA_Conv

section X5mod_RA_Sel
open Matrix Finset Filter Topology Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5RA
open QAlgorithms X5PK X5QC X5PN QAlgorithms.Papers.Independent.Independent1.P04
set_option linter.unusedSectionVars false

section iso
variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

lemma iso_pow {E : Matrix m k ℂ} (hE : Eᴴ * E = 1) (B : Matrix k k ℂ) (n : ℕ) :
    Eᴴ * (E * B * Eᴴ) ^ n = B ^ n * Eᴴ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← Matrix.mul_assoc Eᴴ,
      ← Matrix.mul_assoc Eᴴ, hE, Matrix.one_mul, pow_succ, Matrix.mul_assoc]

lemma iso_aeval {E : Matrix m k ℂ} (hE : Eᴴ * E = 1) (B : Matrix k k ℂ) (p : ℝ[X]) :
    aeval B p = Eᴴ * aeval (E * B * Eᴴ) p * E := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, iso_pow hE, Matrix.mul_assoc, hE, Matrix.mul_one]

lemma iso_cfc {E : Matrix m k ℂ} (hE : Eᴴ * E = 1) {B : Matrix k k ℂ} (hB : B.IsHermitian)
    (f : ℝ → ℝ) : cfc f B = Eᴴ * cfc f (E * B * Eᴴ) * E := by
  have hB' : (E * B * Eᴴ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, conjTranspose_conjTranspose, hB.eq,
      Matrix.mul_assoc]
  exact cfc_transfer hB' hB (fun Z => Eᴴ * Z * E) (iso_aeval hE B) f

lemma relEnt_iso {E : Matrix m k ℂ} (hE : Eᴴ * E = 1) {A B : Matrix k k ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : relEntropy (E * A * Eᴴ) (E * B * Eᴴ) = relEntropy A B := by
  have tr : ∀ M : Matrix m m ℂ, (E * A * Eᴴ * M).trace = (A * (Eᴴ * M * E)).trace := fun M => by
    rw [show E * A * Eᴴ * M = E * (A * Eᴴ * M) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [relEnt_def, relEnt_def, Matrix.trace_sub, Matrix.trace_sub, tr, tr, ← iso_cfc hE hA,
    ← iso_cfc hE hB]
end iso

section scale
variable {k : Type*} [Fintype k] [DecidableEq k]

lemma tr_smul_re (c : ℝ) (X M : Matrix k k ℂ) :
    (((c : ℂ) • X) * M).trace.re = c * (X * M).trace.re := by
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

lemma ker_smul {c : ℂ} (hc : c ≠ 0) (X : Matrix k k ℂ) :
    LinearMap.ker ((c • X).mulVecLin) = LinearMap.ker X.mulVecLin := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.smul_mulVec, smul_eq_zero, hc,
    false_or]

lemma relEnt_norm {X Y : Matrix k k ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hker : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) {p q : ℝ} (hp : 0 < p)
    (hq : 0 < q) (hpX : X.trace.re = p) :
    relEntropy (((p⁻¹ : ℝ) : ℂ) • X) (((q⁻¹ : ℝ) : ℂ) • Y) =
      p⁻¹ * relEntropy X Y - Real.log p + Real.log q := by
  have hc : ((p⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_pos.2 hp).ne'
  have hρ : (((p⁻¹ : ℝ) : ℂ) • X).PosSemidef := by
    rw [Complex.coe_smul]; exact hX.smul (inv_pos.2 hp).le
  have k1 : LinearMap.ker X.mulVecLin ≤ LinearMap.ker (((p⁻¹ : ℝ) : ℂ) • X).mulVecLin := by
    rw [ker_smul hc]
  have k2 : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker (((p⁻¹ : ℝ) : ℂ) • X).mulVecLin := by
    rw [ker_smul hc]; exact hker
  have htr : (((p⁻¹ : ℝ) : ℂ) • X).trace.re = 1 := by
    rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, hpX, inv_mul_cancel₀ hp.ne']
  rw [relEnt_def, Matrix.trace_sub, Complex.sub_re, X5PR.tr_log_smul hρ hX k1 (inv_pos.2 hp),
    X5PR.tr_log_smul hρ hY k2 (inv_pos.2 hq), htr, tr_smul_re, tr_smul_re, relEnt_def,
    Matrix.trace_sub, Complex.sub_re, Real.log_inv, Real.log_inv]
  ring
end scale

section sel

lemma psd_zero {k : Type*} [Fintype k] [DecidableEq k] {X : Matrix k k ℂ} (hX : X.PosSemidef)
    (h : X.trace.re = 0) : X = 0 := by
  apply hX.trace_eq_zero_iff.1
  rw [X5PK.tr_re hX, h]; simp

lemma eq_zero_of_ker {k : Type*} [Fintype k] [DecidableEq k] {X : Matrix k k ℂ}
    (h : ∀ v, X *ᵥ v = 0) : X = 0 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

variable {d : ℕ}

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma conj_eq {e : ℕ} (K : Matrix (Fin e) (Fin d) ℂ) (Z : CoherenceMatrix d) :
    X5DP.Φ (fun _ : Fin 1 => K) Z = conjSuperop K Z := by
  simp [X5DP.Φ, conjSuperop]

/-- one branch of a selective incoherent operation -/
lemma branch {e : ℕ} (he : 0 < e) (K : Matrix (Fin e) (Fin d) ℂ) (hK : PreservesDiagonalBranch K)
    {ρ : CoherenceMatrix d} (hρ : IsDensityMatrix ρ) :
    selectiveContribution entropyCoherence K ρ ≤
      relEntropy (conjSuperop K ρ) (conjSuperop K (dephasedMatrix ρ)) -
        ((conjSuperop K ρ).trace.re * Real.log (conjSuperop K ρ).trace.re -
          (conjSuperop K ρ).trace.re * Real.log (conjSuperop K (dephasedMatrix ρ)).trace.re) := by
  haveI : Nonempty (Fin e) := ⟨⟨0, he⟩⟩
  have hΔ := deph_dens hρ
  set X := conjSuperop K ρ with hXdef
  set Y := conjSuperop K (dephasedMatrix ρ) with hYdef
  have hX : X.PosSemidef := hρ.1.mul_mul_conjTranspose_same K
  have hY : Y.PosSemidef := hΔ.1.mul_mul_conjTranspose_same K
  have hker : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin := by
    have := X5DP.Φ_supp (fun _ : Fin 1 => K) hρ.1 hΔ.1 (ker_deph hρ.1)
    rwa [conj_eq, conj_eq] at this
  have hYd : BasisDiagonal Y := hK _ hΔ.1 (deph_basis ρ)
  set p := X.trace.re
  set q := Y.trace.re
  have hp0 : 0 ≤ p := (Complex.nonneg_iff.1 hX.trace_nonneg).1
  have hq0 : 0 ≤ q := (Complex.nonneg_iff.1 hY.trace_nonneg).1
  unfold selectiveContribution branchProbability
  simp only
  rw [← hXdef]
  split_ifs with hp
  · have hq : 0 < q := by
      rcases hq0.lt_or_eq with h | h
      · exact h
      · exfalso
        have hY0 := psd_zero hY h.symm
        have hX0 : X = 0 := eq_zero_of_ker fun v => by
          have := hker (show v ∈ LinearMap.ker Y.mulVecLin by simp [hY0])
          simpa using this
        simp [p, hX0] at hp
    have e1 : ((p : ℂ)⁻¹) • X = ((p⁻¹ : ℝ) : ℂ) • X := by rw [Complex.ofReal_inv]
    rw [e1]
    set ρ' := ((p⁻¹ : ℝ) : ℂ) • X
    set σ' := ((q⁻¹ : ℝ) : ℂ) • Y
    have hpc : ((p⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_pos.2 hp).ne'
    have hqc : ((q⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_pos.2 hq).ne'
    have dens : ∀ {Z : Matrix (Fin e) (Fin e) ℂ} {r : ℝ}, Z.PosSemidef → 0 < r → Z.trace.re = r →
        IsDensityMatrix (((r⁻¹ : ℝ) : ℂ) • Z) := fun {Z r} hZ hr hZr => by
      refine ⟨by rw [Complex.coe_smul]; exact hZ.smul (inv_pos.2 hr).le, ?_⟩
      rw [Matrix.trace_smul, X5PK.tr_re hZ, hZr, smul_eq_mul, ← Complex.ofReal_mul,
        inv_mul_cancel₀ hr.ne', Complex.ofReal_one]
    have hρ' : IsDensityMatrix ρ' := dens hX hp rfl
    have hσ' : IsDensityMatrix σ' := dens hY hq rfl
    have hσd : BasisDiagonal σ' := fun i j h => by simp [σ', hYd i j h]
    have hk' : LinearMap.ker σ'.mulVecLin ≤ LinearMap.ker ρ'.mulVecLin := by
      simp only [ρ', σ']; rw [ker_smul hpc, ker_smul hqc]; exact hker
    have hmin := ec_min hρ' hσ' hσd hk'
    rw [ec_eq hρ'.1]
    have hn := relEnt_norm hX hY hker hp hq rfl
    rw [hn] at hmin
    have := mul_le_mul_of_nonneg_left hmin hp.le
    have e2 : p * (p⁻¹ * relEntropy X Y - Real.log p + Real.log q) =
        relEntropy X Y - (p * Real.log p - p * Real.log q) := by
      have : p * p⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
      linear_combination relEntropy X Y * this
    linarith
  · have hp' : p = 0 := le_antisymm (not_lt.1 hp) hp0
    have hX0 : X = 0 := psd_zero hX hp'
    rw [hp', hX0]
    simp [relEnt_def]

end sel

end X5RA
end X5mod_RA_Sel

section X5mod_RA_Main
open Matrix Finset Filter Topology Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5RA
open QAlgorithms X5PK X5QC X5PN QAlgorithms.Papers.Independent.Independent1.P04
set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- inclusion `Fin k → Fin N` -/
def incl (k N : ℕ) : Matrix (Fin N) (Fin k) ℂ := fun r c => if (r : ℕ) = c then 1 else 0

lemma incl_iso {k N : ℕ} (h : k ≤ N) : (incl k N)ᴴ * incl k N = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, incl, Matrix.one_apply]
  rw [Finset.sum_eq_single ⟨i, lt_of_lt_of_le i.2 h⟩]
  · by_cases hij : i = j
    · subst hij; simp
    · have : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
      simp [this, hij]
  · intro r _ hr
    have : (r : ℕ) ≠ i := fun e => hr (Fin.ext e)
    simp [this]
  · simp

variable {d a N : ℕ}

/-- flagged Kraus operator -/
def Lm (i : Fin a) (M : Matrix (Fin N) (Fin d) ℂ) : Matrix (Fin a × Fin N) (Fin d) ℂ :=
  fun x y => if x.1 = i then M x.2 y else 0

lemma Lm_iso (i : Fin a) (M : Matrix (Fin N) (Fin d) ℂ) : (Lm i M)ᴴ * Lm i M = Mᴴ * M := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Lm, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma Lm_conj (i : Fin a) (M : Matrix (Fin N) (Fin d) ℂ) (X : CoherenceMatrix d)
    (x x' : Fin a × Fin N) :
    (Lm i M * X * (Lm i M)ᴴ) x x' = if x.1 = i ∧ x'.1 = i then (M * X * Mᴴ) x.2 x'.2 else 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Lm]
  by_cases h1 : x.1 = i <;> by_cases h2 : x'.1 = i <;> simp [h1, h2]

lemma Φ_Lm (M : Fin a → Matrix (Fin N) (Fin d) ℂ) (X : CoherenceMatrix d) :
    X5DP.Φ (fun i => Lm i (M i)) X = bd (fun i => M i * X * (M i)ᴴ) := by
  ext x x'
  simp only [X5DP.Φ, Matrix.sum_apply, Lm_conj, bd]
  by_cases h : x.1 = x'.1
  · rw [if_pos h, Finset.sum_eq_single x.1]
    · simp [h]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]; rintro ⟨h1, h2⟩; exact h (h1.trans h2.symm)

theorem ec_sel : CoherenceSelective entropyCoherence := by
  intro d hd a dims hdims K hK ρ hρ
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exfalso; subst h
      have := hK.1
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at this
      have h1 := congrFun (congrFun this ⟨0, hd⟩) ⟨0, hd⟩
      simp at h1
    · exact h
  set N := Finset.univ.sup dims
  have hN : ∀ i, dims i ≤ N := fun i => Finset.le_sup (Finset.mem_univ i)
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  haveI : Nonempty (Fin N) := ⟨⟨0, lt_of_lt_of_le (hdims ⟨0, ha⟩) (hN _)⟩⟩
  set M : Fin a → Matrix (Fin N) (Fin d) ℂ := fun i => incl (dims i) N * K i
  set L := fun i => Lm i (M i)
  have hL : ∑ i, (L i)ᴴ * L i = 1 := by
    simp only [L, Lm_iso, M, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc (incl _ N)ᴴ, incl_iso (hN _), Matrix.one_mul]
    exact hK.1
  have hΔ := deph_dens hρ
  have hdpi := chan_dpi L hL hρ hΔ (ker_deph hρ.1)
  have hMX : ∀ i (X : CoherenceMatrix d), M i * X * (M i)ᴴ =
      incl (dims i) N * conjSuperop (K i) X * (incl (dims i) N)ᴴ := fun i X => by
    simp only [M, conjSuperop, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have herm : ∀ i (X : CoherenceMatrix d), X.IsHermitian → (conjSuperop (K i) X).IsHermitian :=
    fun i X hX => by
      unfold conjSuperop Matrix.IsHermitian
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, conjTranspose_conjTranspose, hX.eq,
        Matrix.mul_assoc]
  rw [Φ_Lm, Φ_Lm, relEnt_bd (fun i => Matrix.isHermitian_mul_mul_conjTranspose _ hρ.1.1)
    (fun i => Matrix.isHermitian_mul_mul_conjTranspose _ hΔ.1.1)] at hdpi
  simp only [hMX, relEnt_iso (incl_iso (hN _)) (herm _ _ hρ.1.1) (herm _ _ hΔ.1.1)] at hdpi
  set X := fun i => conjSuperop (K i) ρ
  set Y := fun i => conjSuperop (K i) (dephasedMatrix ρ)
  set p := fun i => (X i).trace.re
  set q := fun i => (Y i).trace.re
  have hb : ∀ i, selectiveContribution entropyCoherence (K i) ρ ≤
      relEntropy (X i) (Y i) - (p i * Real.log (p i) - p i * Real.log (q i)) :=
    fun i => branch (hdims i) (K i) (hK.2 i) hρ
  have trsum : ∀ Z : CoherenceMatrix d, ∑ i, (conjSuperop (K i) Z).trace.re = Z.trace.re := by
    intro Z
    have e : ∀ i, (conjSuperop (K i) Z).trace = ((K i)ᴴ * K i * Z).trace := fun i => by
      unfold conjSuperop; rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    simp only [e]
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, hK.1, Matrix.one_mul]
  have hp0 : ∀ i, 0 ≤ p i := fun i =>
    (Complex.nonneg_iff.1 (hρ.1.mul_mul_conjTranspose_same (K i)).trace_nonneg).1
  have hq0 : ∀ i, 0 ≤ q i := fun i =>
    (Complex.nonneg_iff.1 (hΔ.1.mul_mul_conjTranspose_same (K i)).trace_nonneg).1
  have hsupp : ∀ i, q i = 0 → p i = 0 := by
    intro i hqi
    have hY0 := psd_zero (hΔ.1.mul_mul_conjTranspose_same (K i)) hqi
    have hker := X5DP.Φ_supp (fun _ : Fin 1 => K i) hρ.1 hΔ.1 (ker_deph hρ.1)
    rw [conj_eq, conj_eq] at hker
    have hX0 : X i = 0 := eq_zero_of_ker fun v => by
      have := hker (show v ∈ LinearMap.ker (conjSuperop (K i) (dephasedMatrix ρ)).mulVecLin by
        simp only [conjSuperop] at hY0 ⊢; simp [hY0])
      simpa using this
    simp only [p, hX0, Matrix.trace_zero, Complex.zero_re]
  have hkl := kl_nonneg' p q hp0 hq0 hsupp (by simp only [p, X]; rw [trsum, hρ.2]; simp)
    (by simp only [q, Y]; rw [trsum, hΔ.2]; simp)
  rw [ec_eq hρ.1]
  calc ∑ i, selectiveContribution entropyCoherence (K i) ρ
      ≤ ∑ i, (relEntropy (X i) (Y i) - (p i * Real.log (p i) - p i * Real.log (q i))) :=
        Finset.sum_le_sum fun i _ => hb i
    _ = ∑ i, relEntropy (X i) (Y i) - ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) :=
        Finset.sum_sub_distrib _ _
    _ ≤ ∑ i, relEntropy (X i) (Y i) := by linarith
    _ ≤ _ := hdpi

theorem ra_main :
    CoherenceNonnegative entropyCoherence ∧ CoherenceFaithful entropyCoherence ∧
    CoherenceMonotone entropyCoherence ∧ CoherenceSelective entropyCoherence ∧
    CoherenceConvex entropyCoherence :=
  ⟨fun _ hd _ hρ => ec_nonneg hd hρ, fun _ hd _ hρ => ec_faithful hd hρ, ec_mono, ec_sel,
    ec_convex⟩

end X5RA
end X5mod_RA_Main

set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Independent1.P04

theorem solution :
    CoherenceNonnegative entropyCoherence ∧ CoherenceFaithful entropyCoherence ∧
    CoherenceMonotone entropyCoherence ∧ CoherenceSelective entropyCoherence ∧
    CoherenceConvex entropyCoherence := X5RA.ra_main

end
