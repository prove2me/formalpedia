-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_8
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:45:19.526265+00:00
-- url     : https://prove2.me/submissions/69c1b960-6dd0-4f75-8888-04eec285424d

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

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

lemma spec_mulVec {R : Matrix I I ℂ} (hR : R.IsHermitian) (x : I → ℂ) :
    R *ᵥ x = (hR.eigenvectorUnitary : Matrix I I ℂ) *ᵥ
      (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hR.eigenvalues) *ᵥ (star (hR.eigenvectorUnitary : Matrix I I ℂ) *ᵥ x)) := by
  conv_lhs => rw [hR.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, ← mulVec_mulVec, ← mulVec_mulVec]

lemma supp_bwd {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian)
    (h : ∀ i j, hR.eigenvalues i ≠ 0 → hN.eigenvalues j = 0 → ov hR hN i j = 0) :
    LinearMap.ker N.mulVecLin ≤ LinearMap.ker R.mulVecLin := by
  intro x hx
  rw [LinearMap.mem_ker, mulVecLin_apply] at hx ⊢
  set U := (hR.eigenvectorUnitary : Matrix I I ℂ)
  set V := (hN.eigenvectorUnitary : Matrix I I ℂ)
  have hV : V * star V = 1 := Unitary.mul_star_self_of_mem (hN.eigenvectorUnitary).2
  have hV' : star V * V = 1 := Unitary.star_mul_self_of_mem (hN.eigenvectorUnitary).2
  set c := star V *ᵥ x
  have hc : ∀ j, hN.eigenvalues j ≠ 0 → c j = 0 := by
    intro j hj
    have h1 : star V *ᵥ (N *ᵥ x) = 0 := by rw [hx, mulVec_zero]
    rw [spec_mulVec hN, mulVec_mulVec, hV', one_mulVec] at h1
    have := congrFun h1 j
    rw [mulVec_diagonal] at this
    simp only [Function.comp_apply, Pi.zero_apply] at this
    rcases mul_eq_zero.1 this with h2 | h2
    · exact absurd (by simpa using h2) hj
    · exact h2
  have hUx : star U *ᵥ x = ov hR hN *ᵥ c := by
    rw [show ov hR hN = star U * V from rfl, mulVec_mulVec, Matrix.mul_assoc, hV, Matrix.mul_one]
  have hD : diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hR.eigenvalues) *ᵥ (star U *ᵥ x) = 0 := by
    ext i
    rw [hUx, mulVec_diagonal, Pi.zero_apply]
    by_cases hi : hR.eigenvalues i = 0
    · simp [hi]
    · simp only [mulVec, dotProduct]
      rw [Finset.sum_eq_zero, mul_zero]
      intro j _
      by_cases hj : hN.eigenvalues j = 0
      · rw [h i j hi hj, zero_mul]
      · rw [hc j hj, mul_zero]
  rw [spec_mulVec hR, hD, mulVec_zero]

end X5OL
end X5mod_OL_Base

section X5mod_B2_Main
open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace X5B2

section Scalar
variable {ι : Type*} [Fintype ι]
variable {l m : ι → ℝ} {W : ι → ι → ℝ}

noncomputable def Tset (l : ι → ℝ) (W : ι → ι → ℝ) : Finset (ι × ι) :=
  univ.filter fun p => W p.1 p.2 ≠ 0 ∧ l p.2 ≠ 0

lemma sumT {f : ι × ι → ℝ} (hf : ∀ p, W p.1 p.2 = 0 ∨ l p.2 = 0 → f p = 0) :
    ∑ p ∈ Tset l W, f p = ∑ i, ∑ j, f (i, j) := by
  rw [← Fintype.sum_prod_type]
  refine Finset.sum_filter_of_ne fun p _ h => ?_
  by_contra hc
  rw [not_and_or, not_not, not_not] at hc
  exact h (hf p hc)

noncomputable def D (l m : ι → ℝ) (W : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, (l j * Real.log (l j) - Real.log (m i) * l j) * W i j

noncomputable def Sh (l m : ι → ℝ) (W : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, Real.sqrt (m i) * Real.sqrt (l j) * W i j

variable (hW : ∀ i j, 0 ≤ W i j) (hcol : ∀ j, ∑ i, W i j = 1) (hl : ∀ j, 0 ≤ l j)
  (hm : ∀ i, 0 ≤ m i) (hs : ∀ i j, W i j ≠ 0 → l j ≠ 0 → m i ≠ 0)

include hl hm hs in
lemma pos {p : ι × ι} (hp : p ∈ Tset l W) : 0 < l p.2 ∧ 0 < m p.1 := by
  obtain ⟨h1, h2⟩ := (mem_filter.1 hp).2
  exact ⟨lt_of_le_of_ne (hl _) (Ne.symm h2), lt_of_le_of_ne (hm _) (Ne.symm (hs _ _ h1 h2))⟩

include hW hcol hl hm hs in
/-- Jensen at order one half: `-2 log (S_{1/2}/T) ≤ D/T` with `T = Σ l` -/
theorem half (hT : 0 < ∑ j, l j) :
    0 < Sh l m W ∧ -2 * Real.log (Sh l m W / ∑ j, l j) ≤ D l m W / ∑ j, l j := by
  set T := ∑ j, l j
  have hq : ∑ p ∈ Tset l W, W p.1 p.2 * l p.2 / T = 1 := by
    rw [← Finset.sum_div, sumT (f := fun p => W p.1 p.2 * l p.2) (by rintro p (h | h) <;> simp [h])]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hcol, one_mul]
    exact div_self hT.ne'
  have hwn : ∀ p ∈ Tset l W, 0 ≤ W p.1 p.2 * l p.2 / T :=
    fun p _ => div_nonneg (mul_nonneg (hW _ _) (hl _)) hT.le
  have hxp : ∀ p ∈ Tset l W, 0 < Real.sqrt (m p.1 / l p.2) := fun p hp =>
    Real.sqrt_pos.2 (div_pos (pos hl hm hs hp).2 (pos hl hm hs hp).1)
  have e2 : ∑ p ∈ Tset l W, W p.1 p.2 * l p.2 / T * Real.sqrt (m p.1 / l p.2) = Sh l m W / T := by
    unfold Sh
    rw [← sumT (l := l) (W := W) (f := fun p => Real.sqrt (m p.1) * Real.sqrt (l p.2) * W p.1 p.2)
      (by rintro p (h | h) <;> simp [h]), Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨a, b⟩ := pos hl hm hs hp
    rw [Real.sqrt_div' _ a.le]
    have hsa : 0 < Real.sqrt (l p.2) := Real.sqrt_pos.2 a
    field_simp
    simp only [Real.sq_sqrt a.le]
  have hSpos : 0 < Sh l m W / T := by
    rw [← e2]
    by_contra hc
    push_neg at hc
    have : ∑ p ∈ Tset l W, W p.1 p.2 * l p.2 / T ≤ 0 := by
      refine (Finset.sum_le_sum fun p hp => ?_).trans_eq (Finset.sum_const_zero)
      by_contra h'
      push_neg at h'
      have := Finset.sum_pos' (s := Tset l W)
        (f := fun p => W p.1 p.2 * l p.2 / T * Real.sqrt (m p.1 / l p.2))
        (fun q hq => mul_nonneg (hwn q hq) (hxp q hq).le) ⟨p, hp, mul_pos h' (hxp p hp)⟩
      linarith
    linarith
  refine ⟨(div_pos_iff_of_pos_right hT).1 hSpos, ?_⟩
  have J := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := Tset l W)
    (w := fun p => W p.1 p.2 * l p.2 / T) (p := fun p => Real.sqrt (m p.1 / l p.2))
    hwn hq hxp
  simp only [smul_eq_mul] at J
  rw [e2] at J
  have e1 : ∑ p ∈ Tset l W, W p.1 p.2 * l p.2 / T * Real.log (Real.sqrt (m p.1 / l p.2)) =
      -(D l m W / T) / 2 := by
    have hD : D l m W = ∑ p ∈ Tset l W, W p.1 p.2 * l p.2 * (Real.log (l p.2) - Real.log (m p.1)) := by
      unfold D
      rw [sumT (f := fun p => W p.1 p.2 * l p.2 * (Real.log (l p.2) - Real.log (m p.1)))
        (by rintro p (h | h) <;> simp [h])]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hD, Finset.sum_div, ← Finset.sum_neg_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨a, b⟩ := pos hl hm hs hp
    rw [Real.log_sqrt (div_nonneg b.le a.le), Real.log_div b.ne' a.ne']
    ring
  rw [e1] at J
  linarith

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

/-- `Re Tr Z ≤ Tr √(Z Z†)` -/
theorem re_tr_le (Z : Matrix I I ℂ) : Z.trace.re ≤ (cfc Real.sqrt (Z * Zᴴ)).trace.re := by
  set M := Z * Zᴴ
  have hM : M.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose Z
  have hMs : IsSelfAdjoint M := hM.1.isSelfAdjoint
  have hspec : ∀ x ∈ spectrum ℝ M, 0 ≤ x := fun x hx => spectrum_nonneg_of_nonneg hM.nonneg hx
  have key : ∀ ε : ℝ, 0 < ε → Z.trace.re ≤ (cfc Real.sqrt M).trace.re + ε * Fintype.card I / 2 := by
    intro ε hε
    set L := cfc (fun x => Real.sqrt (Real.sqrt x + ε)) M
    set K := cfc (fun x => (Real.sqrt (Real.sqrt x + ε))⁻¹) M
    have hpos : ∀ x : ℝ, 0 < Real.sqrt (Real.sqrt x + ε) :=
      fun x => Real.sqrt_pos.2 (by positivity)
    have hLK : L * K = 1 := by
      rw [← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_const_one ℝ M]
      exact cfc_congr fun x _ => mul_inv_cancel₀ (hpos x).ne'
    have hKL : K * L = 1 := by
      rw [← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_const_one ℝ M]
      exact cfc_congr fun x _ => inv_mul_cancel₀ (hpos x).ne'
    have hLh : Lᴴ = L := (cfc_predicate _ M : IsSelfAdjoint L)
    have hKh : Kᴴ = K := (cfc_predicate _ M : IsSelfAdjoint K)
    have h := cs L (K * Z)
    have e1 : Lᴴ * (K * Z) = Z := by rw [hLh, ← Matrix.mul_assoc, hLK, Matrix.one_mul]
    have e2 : (K * Z)ᴴ * L = Zᴴ := by
      rw [conjTranspose_mul, hKh, Matrix.mul_assoc, hKL, Matrix.mul_one]
    have e3 : (Lᴴ * L).trace.re = (cfc Real.sqrt M).trace.re + ε * Fintype.card I := by
      have : Lᴴ * L = cfc Real.sqrt M + (ε : ℂ) • 1 := by
        rw [hLh, ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
        rw [show (ε : ℂ) • (1 : Matrix I I ℂ) = cfc (fun _ : ℝ => ε) M by
          rw [cfc_const ε M hMs]; simp [Algebra.algebraMap_eq_smul_one]]
        rw [← cfc_add _ _ _ (fin _ _) (fin _ _)]
        refine cfc_congr fun x hx => ?_
        exact Real.mul_self_sqrt (by have := Real.sqrt_nonneg x; linarith)
      rw [this, Matrix.trace_add, Complex.add_re, Matrix.trace_smul, Matrix.trace_one]
      simp
    have e4 : ((K * Z)ᴴ * (K * Z)).trace.re ≤ (cfc Real.sqrt M).trace.re := by
      have t1 : ((K * Z)ᴴ * (K * Z)).trace = (K * K * M).trace := by
        rw [conjTranspose_mul, hKh]
        rw [show Zᴴ * K * (K * Z) = Zᴴ * (K * K * Z) by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm]
        simp only [M, Matrix.mul_assoc]
      have t2 : K * K * M = cfc (fun x => x / (Real.sqrt x + ε)) M := by
        rw [show K * K * M = K * K * cfc (fun x : ℝ => x) M by rw [cfc_id' ℝ M hMs],
          ← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
        refine cfc_congr fun x hx => ?_
        have h0 := hspec x hx
        have h1 : 0 < Real.sqrt x + ε := by positivity
        rw [← mul_inv, Real.mul_self_sqrt h1.le, div_eq_inv_mul]
      have t3 : (cfc Real.sqrt M - K * K * M).PosSemidef := by
        rw [t2, ← cfc_sub _ _ _ (fin _ _) (fin _ _)]
        refine (cfc_nonneg (fun x hx => ?_) :
          0 ≤ cfc (fun x => Real.sqrt x - x / (Real.sqrt x + ε)) M).posSemidef
        have h0 := hspec x hx
        have h1 : 0 < Real.sqrt x + ε := by positivity
        rw [sub_nonneg, div_le_iff₀ h1]
        have := Real.mul_self_sqrt h0
        nlinarith [Real.sqrt_nonneg x]
      have := psd_re t3
      rw [Matrix.trace_sub, Complex.sub_re] at this
      rw [t1]; linarith
    rw [e1, e2, e3, Matrix.trace_conjTranspose] at h
    simp only [RCLike.star_def, Complex.conj_re] at h
    linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hc : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have := key (2 * δ / (Fintype.card I + 1)) (by positivity)
  refine this.trans ?_
  have : 2 * δ / (Fintype.card I + 1) * Fintype.card I / 2 ≤ δ := by
    rw [div_mul_eq_mul_div, div_div, div_le_iff₀ (by positivity)]
    nlinarith
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

lemma sqrt_herm (X : Matrix I I ℂ) : (cfc Real.sqrt X)ᴴ = cfc Real.sqrt X :=
  (cfc_predicate Real.sqrt X : IsSelfAdjoint _)

lemma sqrt_sq {X : Matrix I I ℂ} (hX : X.PosSemidef) : cfc Real.sqrt X * cfc Real.sqrt X = X := by
  have hs : IsSelfAdjoint X := hX.1.isSelfAdjoint
  rw [← cfc_mul _ _ _ (fin _ _) (fin _ _)]
  conv_rhs => rw [← cfc_id' ℝ X hs]
  refine cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hX.nonneg hx)

end Mat

end X5B2

namespace X5B2
open QAlgorithms.Papers.Independent.Claimed50.P12

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma D_eq {X Y : Matrix I I ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (cfc (fun x : ℝ => x * Real.log x) X - X * cfc Real.log Y).trace.re =
      D hX.eigenvalues hY.eigenvalues (X5OL.w hY hX) := by
  unfold D
  have e1 : cfc (fun x : ℝ => x * Real.log x) X =
      cfc (fun _ : ℝ => (1 : ℝ)) Y * cfc (fun x : ℝ => x * Real.log x) X := by
    rw [cfc_const_one ℝ Y, Matrix.one_mul]
  have e2 : (X * cfc Real.log Y).trace = (cfc Real.log Y * cfc (fun x : ℝ => x) X).trace := by
    rw [cfc_id' ℝ X hX.isSelfAdjoint, Matrix.trace_mul_comm]
  rw [Matrix.trace_sub, e2, e1, X5OL.tr_cfc_cfc hY hX, X5OL.tr_cfc_cfc hY hX, Complex.sub_re,
    Complex.re_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.re_sum, Complex.ofReal_re, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma Sh_eq {X Y : Matrix I I ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (cfc Real.sqrt X * cfc Real.sqrt Y).trace.re =
      Sh hX.eigenvalues hY.eigenvalues (X5OL.w hY hX) := by
  rw [Matrix.trace_mul_comm, X5OL.tr_cfc_cfc hY hX, Complex.re_sum]
  unfold Sh
  simp only [Complex.re_sum, Complex.ofReal_re]

theorem main [Nonempty I] (rho sigma : Matrix I I ℂ) (hrho : rho.PosSemidef)
    (hsigma : sigma.PosSemidef) (htrace : 0 < rho.trace.re) :
    negLogBits (ENNReal.ofReal ((QAlgorithms.rootFidelity rho sigma / rho.trace.re) ^ 2)) ≤
      normalizedRelativeEntropyBits rho sigma := by
  have hne : rho ≠ 0 := by rintro rfl; simp at htrace
  unfold normalizedRelativeEntropyBits
  rw [if_neg hne]
  unfold QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy
  have hc : (0 : ℝ) < (rho.trace.re * Real.log 2)⁻¹ :=
    inv_pos.2 (mul_pos htrace (Real.log_pos (by norm_num)))
  split_ifs with hs
  swap
  · rw [EReal.top_mul_of_pos (EReal.coe_pos.2 hc)]; exact le_top
  have hX := hrho.1
  have hY := hsigma.1
  set l := hX.eigenvalues
  set m := hY.eigenvalues
  set W := X5OL.w hY hX
  have hT : rho.trace.re = ∑ j, l j := by
    rw [hX.trace_eq_sum_eigenvalues, Complex.re_sum]; simp [l]
  have hsW : ∀ i j, W i j ≠ 0 → l j ≠ 0 → m i ≠ 0 := by
    intro i j hw hl hm
    apply hw
    simp only [W]
    rw [w_swap hX hY j i]
    simp [X5OL.w, X5OL.supp_fwd hX hY hs j i hl hm]
  obtain ⟨hSpos, hJ⟩ := half (l := l) (m := m) (W := W) (X5OL.w_nonneg hY hX) (w_col hY hX)
    hrho.eigenvalues_nonneg hsigma.eigenvalues_nonneg hsW (by rw [← hT]; exact htrace)
  rw [← hT, ← Sh_eq hX hY, ← D_eq hX hY] at hJ
  rw [← Sh_eq hX hY] at hSpos
  set S := (cfc Real.sqrt rho * cfc Real.sqrt sigma).trace.re
  set F := QAlgorithms.rootFidelity rho sigma
  set T := rho.trace.re
  set Dv := (cfc (fun x : ℝ => x * Real.log x) rho - rho * cfc Real.log sigma).trace.re
  have hSF : S ≤ F := by
    have := re_tr_le (cfc Real.sqrt rho * cfc Real.sqrt sigma)
    rw [conjTranspose_mul, sqrt_herm, sqrt_herm,
      show cfc Real.sqrt rho * cfc Real.sqrt sigma * (cfc Real.sqrt sigma * cfc Real.sqrt rho) =
        cfc Real.sqrt rho * (cfc Real.sqrt sigma * cfc Real.sqrt sigma) * cfc Real.sqrt rho by
        simp only [Matrix.mul_assoc], sqrt_sq hsigma] at this
    exact this
  have hy : 0 < (F / T) ^ 2 := by
    have : 0 < F / T := div_pos (hSpos.trans_le hSF) htrace
    positivity
  unfold negLogBits
  rw [if_neg (by rw [ENNReal.ofReal_eq_zero]; exact not_le.2 hy), if_neg ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hy.le, ← EReal.coe_mul, EReal.coe_le_coe_iff]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log (S / T) ≤ Real.log (F / T) :=
    Real.log_le_log (div_pos hSpos htrace) (div_le_div_of_nonneg_right hSF htrace.le)
  rw [Real.logb, Real.log_pow, mul_inv, ← mul_assoc, ← div_eq_mul_inv Dv]
  rw [show -((((2 : ℕ) : ℝ) * Real.log (F / T)) / Real.log 2) =
    (-2 * Real.log (F / T)) / Real.log 2 by push_cast; ring]
  rw [div_le_iff₀ hl2]
  have : -2 * Real.log (F / T) ≤ Dv / T := by linarith
  calc -2 * Real.log (F / T) ≤ Dv / T := this
    _ = Dv / T * (Real.log 2)⁻¹ * Real.log 2 := by field_simp

end X5B2
end X5mod_B2_Main

section X5mod_UH_Base
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder

namespace X5UH
set_option linter.unusedSectionVars false

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

lemma tr_pow_swap (X : Matrix m n ℂ) (k : ℕ) :
    ((Xᴴ * X) ^ (k + 1)).trace = ((X * Xᴴ) ^ (k + 1)).trace := by
  have h : ∀ k : ℕ, (Xᴴ * X) ^ (k + 1) = Xᴴ * (X * Xᴴ) ^ k * X := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← pow_succ']

lemma tr_aeval_swap (X : Matrix m n ℂ) (p : ℝ[X]) (hp : p.coeff 0 = 0) :
    (aeval (Xᴴ * X) p).trace = (aeval (X * Xᴴ) p).trace := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [hp]
  · rw [tr_pow_swap]

theorem tr_cfc_swap (X : Matrix m n ℂ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f (Xᴴ * X)).trace = (cfc f (X * Xᴴ)).trace := by
  set A := Xᴴ * X
  set B := X * Xᴴ
  have hA : IsSelfAdjoint A := (Matrix.posSemidef_conjTranspose_mul_self X).1.isSelfAdjoint
  have hB : IsSelfAdjoint B := (Matrix.posSemidef_self_mul_conjTranspose X).1.isSelfAdjoint
  have fA : (spectrum ℝ A).Finite := A.finite_real_spectrum
  have fB : (spectrum ℝ B).Finite := B.finite_real_spectrum
  set s : Finset ℝ := {0} ∪ fA.toFinset ∪ fB.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have h1 : cfc f A = cfc (fun x => p.eval x) A :=
    cfc_congr fun x hx => (hp x (by simp [s, fA.mem_toFinset.2 hx])).symm
  have h2 : cfc f B = cfc (fun x => p.eval x) B :=
    cfc_congr fun x hx => (hp x (by simp [s, fB.mem_toFinset.2 hx])).symm
  rw [h1, h2, cfc_polynomial p A hA, cfc_polynomial p B hB]
  refine tr_aeval_swap X p ?_
  rw [Polynomial.coeff_zero_eq_eval_zero, hp 0 (by simp [s]), hf]

end X5UH
end X5mod_UH_Base

section X5mod_UH_Polar
open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace X5UH
set_option linter.unusedSectionVars false

variable {R : Type*} [Fintype R] [DecidableEq R]

lemma dot_self (Y : Matrix R R ℂ) (v : R → ℂ) :
    star (Y *ᵥ v) ⬝ᵥ (Y *ᵥ v) = star v ⬝ᵥ ((Yᴴ * Y) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

lemma norm_sq_eq (x : EuclideanSpace ℂ R) : ((‖x‖ ^ 2 : ℝ) : ℂ) = star (x.ofLp) ⬝ᵥ x.ofLp := by
  rw [Complex.ofReal_pow, show ((‖x‖ : ℂ)) ^ 2 = inner ℂ x x from
    (inner_self_eq_norm_sq_to_K x).symm, PiLp.inner_apply]
  simp [dotProduct, mul_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl

/-- Polar decomposition: `Y = W |Y|` with `W` unitary. -/
theorem polar (Y : Matrix R R ℂ) :
    ∃ W : Matrix.unitaryGroup R ℂ, (W : Matrix R R ℂ) * cfc Real.sqrt (Yᴴ * Y) = Y := by
  set G := Yᴴ * Y
  have hG : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Y
  set A := cfc Real.sqrt G
  set Ap := cfc (fun x => (Real.sqrt x)⁻¹) G
  set P := cfc (fun x => Real.sqrt x * (Real.sqrt x)⁻¹) G
  have hAh : Aᴴ = A := X5B2.sqrt_herm G
  have hAA : A * A = G := X5B2.sqrt_sq hG
  have hApA : Ap * A = P := by
    rw [← cfc_mul _ _ _ (X5B2.fin _ _) (X5B2.fin _ _)]
    exact cfc_congr fun x _ => mul_comm _ _
  have hA1P : A * (1 - P) = 0 := by
    rw [← cfc_one ℝ G, ← cfc_sub _ _ _ (X5B2.fin _ _) (X5B2.fin _ _),
      ← cfc_mul _ _ _ (X5B2.fin _ _) (X5B2.fin _ _)]
    rw [show (0 : Matrix R R ℂ) = cfc (fun _ : ℝ => (0 : ℝ)) G by simp]
    refine cfc_congr fun x _ => ?_
    by_cases h : Real.sqrt x = 0
    · simp [h]
    · simp [mul_inv_cancel₀ h]
  have hY1P : Y * (1 - P) = 0 := by
    have : (Y * (1 - P))ᴴ * (Y * (1 - P)) = 0 := by
      have e : (Y * (1 - P))ᴴ * (Y * (1 - P)) = (A * (1 - P))ᴴ * (A * (1 - P)) := by
        simp only [conjTranspose_mul, hAh]
        rw [show (1 - P)ᴴ * Yᴴ * (Y * (1 - P)) = (1 - P)ᴴ * G * (1 - P) by
            simp only [G, Matrix.mul_assoc],
          ← hAA]
        simp only [Matrix.mul_assoc]
      rw [e, hA1P, Matrix.mul_zero]
    exact Matrix.conjTranspose_mul_self_eq_zero.mp this
  set M := Y * Ap
  have hMA : M * A = Y := by
    rw [Matrix.mul_assoc, hApA]
    have := hY1P
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  -- isometry on the range of A
  have hnorm : ∀ v : R → ℂ, ‖(WithLp.toLp 2 (Y *ᵥ v) : EuclideanSpace ℂ R)‖ =
      ‖(WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R)‖ := by
    intro v
    have h1 := norm_sq_eq (WithLp.toLp 2 (Y *ᵥ v) : EuclideanSpace ℂ R)
    have h2 := norm_sq_eq (WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R)
    simp only [WithLp.ofLp_toLp] at h1 h2
    rw [dot_self] at h1
    rw [dot_self, hAh, hAA] at h2
    rw [← h2] at h1
    have := Complex.ofReal_injective h1
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  set TA := Matrix.toEuclideanLin A
  set S := LinearMap.range TA
  let L : S →ₗᵢ[ℂ] EuclideanSpace ℂ R :=
    { toLinearMap := (Matrix.toEuclideanLin M).domRestrict S
      norm_map' := by
        rintro ⟨s, v, rfl⟩
        simp only [LinearMap.domRestrict_apply, TA, Matrix.toEuclideanLin_apply,
          WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hMA, Submodule.coe_norm]
        exact hnorm _ }
  set W := L.extend
  set Wm := Matrix.toEuclideanLin.symm W.toLinearMap
  have hW : ∀ x, Matrix.toEuclideanLin Wm x = W x := by
    intro x; simp [Wm]
  have hWv : ∀ u : R → ℂ, Wm *ᵥ u = (W (WithLp.toLp 2 u)).ofLp := by
    intro u; rw [← hW]; simp
  have hWA : Wm * A = Y := by
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    rw [← Matrix.mulVec_mulVec, hWv]
    have hx : (WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R) ∈ S := ⟨WithLp.toLp 2 v, by simp [TA]⟩
    have := L.extend_apply ⟨_, hx⟩
    simp only at this
    rw [this]
    simp [L, Matrix.mulVec_mulVec, hMA]
  have hU : Wm ∈ Matrix.unitaryGroup R ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    have := W.inner_map_map (EuclideanSpace.single i (1 : ℂ)) (EuclideanSpace.single j 1)
    have hc : ∀ j : R, (W (EuclideanSpace.single j (1 : ℂ))).ofLp = Wm.col j := by
      intro j; rw [← Matrix.mulVec_single_one, hWv]; rfl
    rw [EuclideanSpace.inner_single_left, PiLp.inner_apply] at this
    simp only [hc] at this
    simp only [star_eq_conjTranspose, Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply]
    convert this using 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.col_apply, RCLike.inner_apply]
      exact mul_comm _ _
    · simp [EuclideanSpace.single_apply, eq_comm]
  exact ⟨⟨Wm, hU⟩, hWA⟩

end X5UH
end X5mod_UH_Polar

section X5mod_UH_Main
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate

namespace X5UH
set_option linter.unusedSectionVars false

variable {D R : Type*} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

lemma psd_tr {X : Matrix R R ℂ} (h : X.PosSemidef) : X.trace = ((X.trace.re : ℝ) : ℂ) := by
  have := h.trace_nonneg
  rw [Complex.nonneg_iff] at this
  exact Complex.ext (by simp) (by simp [← this.2])

/-- `|Tr (Z V)| ≤ Tr √(Z Z†)` for unitary `V`. -/
lemma abs_tr_le (Z V : Matrix R R ℂ) (hV : V * Vᴴ = 1) :
    ‖(Z * V).trace‖ ≤ (cfc Real.sqrt (Z * Zᴴ)).trace.re := by
  set t := (Z * V).trace
  by_cases ht : t = 0
  · rw [ht, norm_zero]
    exact X5B2.psd_re (cfc_nonneg (fun x _ => Real.sqrt_nonneg x) :
      0 ≤ cfc Real.sqrt (Z * Zᴴ)).posSemidef
  set c : ℂ := star t / (‖t‖ : ℂ)
  have hn : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ht
  have hc : c * star c = 1 := by
    simp only [c, star_div₀, star_star, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    rw [div_mul_div_comm, Complex.conj_mul', ← pow_two]
    exact div_self (pow_ne_zero 2 hn)
  have h := X5B2.re_tr_le (c • (Z * V))
  have e1 : (c • (Z * V)) * (c • (Z * V))ᴴ = Z * Zᴴ := by
    rw [conjTranspose_smul, smul_mul_smul_comm, hc, one_smul, conjTranspose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc V, hV, Matrix.one_mul]
  have e2 : (c • (Z * V)).trace.re = ‖t‖ := by
    rw [Matrix.trace_smul, smul_eq_mul]
    simp only [c, Complex.star_def]
    rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rw [pow_two, mul_div_assoc, div_self hn, mul_one]
    simp only [Complex.ofReal_re]; rfl
  rw [e1, e2] at h
  exact h

lemma tr_attain (Z : Matrix R R ℂ) :
    ∃ V : Matrix.unitaryGroup R ℂ, ‖(Z * (V : Matrix R R ℂ)).trace‖ =
      (cfc Real.sqrt (Z * Zᴴ)).trace.re := by
  obtain ⟨W, hW⟩ := polar Zᴴ
  rw [conjTranspose_conjTranspose] at hW
  have hZ : Z = cfc Real.sqrt (Z * Zᴴ) * (W : Matrix R R ℂ)ᴴ := by
    have := congrArg conjTranspose hW
    rw [conjTranspose_conjTranspose, conjTranspose_mul, X5B2.sqrt_herm] at this
    exact this.symm
  refine ⟨W, ?_⟩
  have hWW : (W : Matrix R R ℂ)ᴴ * W = 1 := by
    have := W.2; rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
  nth_rewrite 1 [hZ]
  rw [Matrix.mul_assoc, hWW, Matrix.mul_one]
  have hp : (cfc Real.sqrt (Z * Zᴴ)).PosSemidef :=
    (cfc_nonneg (fun x _ => Real.sqrt_nonneg x) : 0 ≤ cfc Real.sqrt (Z * Zᴴ)).posSemidef
  rw [psd_tr hp, Complex.norm_real, Real.norm_of_nonneg (X5B2.psd_re hp), Complex.ofReal_re]

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

lemma purif_eq {psi : D × R → ℂ} {rho : Matrix D D ℂ} (h : UnnormalizedPurifies psi rho) :
    rho = (Matrix.of fun i r => psi (i, r)) * (Matrix.of fun i r => psi (i, r))ᴴ := by
  rw [← h]
  ext i j
  simp [UnnormalizedPurifies, vectorOuterProduct, QAlgorithms.traceRight, QAlgorithms.pureDensity,
    Matrix.mul_apply]

lemma overlap_eq (psi phi : D × R → ℂ) (U : Matrix R R ℂ) :
    ∑ x : D × R, conj (psi x) * ∑ r : R, U x.2 r * phi (x.1, r) =
      ((Matrix.of fun i r => psi (i, r))ᴴ * (Matrix.of fun i r => phi (i, r)) * Uᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [RCLike.star_def]; ring

lemma fid_eq {rho sigma : Matrix D D ℂ} (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (Ψ Φ : Matrix D R ℂ) (hr : rho = Ψ * Ψᴴ) (hs : sigma = Φ * Φᴴ) :
    (cfc Real.sqrt ((Ψᴴ * Φ) * (Ψᴴ * Φ)ᴴ)).trace.re = QAlgorithms.rootFidelity rho sigma := by
  set a := cfc Real.sqrt rho
  set b := cfc Real.sqrt sigma
  have ha : aᴴ = a := X5B2.sqrt_herm rho
  have hb : bᴴ = b := X5B2.sqrt_herm sigma
  have haa : a * a = rho := X5B2.sqrt_sq hrho
  have hbb : b * b = sigma := X5B2.sqrt_sq hsigma
  have e1 : (Ψᴴ * Φ) * (Ψᴴ * Φ)ᴴ = (b * Ψ)ᴴ * (b * Ψ) := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hb]
    rw [show Ψᴴ * b * (b * Ψ) = Ψᴴ * (b * b) * Ψ by simp only [Matrix.mul_assoc], hbb, hs]
    simp only [Matrix.mul_assoc]
  have e2 : (b * Ψ) * (b * Ψ)ᴴ = (a * b)ᴴ * (a * b) := by
    simp only [conjTranspose_mul, ha, hb]
    rw [show b * a * (a * b) = b * (a * a) * b by simp only [Matrix.mul_assoc], haa, hr]
    simp only [Matrix.mul_assoc]
  have e3 : (a * b) * (a * b)ᴴ = a * sigma * a := by
    simp only [conjTranspose_mul, ha, hb]
    rw [← hbb]; simp only [Matrix.mul_assoc]
  unfold QAlgorithms.rootFidelity
  rw [e1, tr_cfc_swap _ _ Real.sqrt_zero, e2, tr_cfc_swap _ _ Real.sqrt_zero, e3]

theorem uhlmann_greatest
    (rho sigma : Op D) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (psi phi : D × R → ℂ) (hpsi : UnnormalizedPurifies psi rho) (hphi : UnnormalizedPurifies phi sigma) :
    IsGreatest {v : ℝ | ∃ U : Matrix.unitaryGroup R ℂ,
      v = ‖∑ x : D × R, conj (psi x) *
        ∑ r : R, (U : Op R) x.2 r * phi (x.1,r)‖} (QAlgorithms.rootFidelity rho sigma) := by
  set Ψ : Matrix D R ℂ := Matrix.of fun i r => psi (i, r)
  set Φ : Matrix D R ℂ := Matrix.of fun i r => phi (i, r)
  set Z := Ψᴴ * Φ
  have hF := fid_eq hrho hsigma Ψ Φ (purif_eq hpsi) (purif_eq hphi)
  refine ⟨?_, ?_⟩
  · obtain ⟨V, hV⟩ := tr_attain Z
    have hVt : (V : Matrix R R ℂ)ᵀ ∈ Matrix.unitaryGroup R ℂ := by
      rw [Matrix.mem_unitaryGroup_iff']
      have := V.2; rw [Matrix.mem_unitaryGroup_iff] at this
      rw [star_eq_conjTranspose, show ((V : Matrix R R ℂ)ᵀ)ᴴ = ((V : Matrix R R ℂ)ᴴ)ᵀ from rfl,
        ← Matrix.transpose_mul, ← star_eq_conjTranspose, this, Matrix.transpose_one]
    refine ⟨⟨_, hVt⟩, ?_⟩
    rw [overlap_eq]
    simp only [Matrix.transpose_transpose]
    rw [hV, ← hF]
  · rintro v ⟨U, rfl⟩
    rw [overlap_eq, ← hF]
    refine abs_tr_le Z _ ?_
    have := U.2; rw [Matrix.mem_unitaryGroup_iff'] at this
    rw [show ((U : Matrix R R ℂ)ᵀ)ᴴ = ((U : Matrix R R ℂ)ᴴ)ᵀ from rfl, ← Matrix.transpose_mul,
      ← star_eq_conjTranspose, this, Matrix.transpose_one]

theorem uhlmann
    (rho sigma : Op D) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (psi phi : D × R → ℂ) (hpsi : UnnormalizedPurifies psi rho) (hphi : UnnormalizedPurifies phi sigma) :
    QAlgorithms.rootFidelity rho sigma = sSup {v : ℝ | ∃ U : Matrix.unitaryGroup R ℂ,
      v = ‖∑ x : D × R, conj (psi x) *
        ∑ r : R, (U : Op R) x.2 r * phi (x.1,r)‖} :=
  (uhlmann_greatest rho sigma hrho hsigma psi phi hpsi hphi).csSup_eq.symm

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

lemma purif_exists {rho : Matrix X X ℂ} (h : rho.PosSemidef) :
    UnnormalizedPurifies (fun p : X × X => cfc Real.sqrt rho p.1 p.2) rho := by
  have hh := X5B2.sqrt_herm rho
  unfold UnnormalizedPurifies
  conv_rhs => rw [← X5B2.sqrt_sq h]
  ext i j
  simp only [vectorOuterProduct, QAlgorithms.traceRight, QAlgorithms.pureDensity, Matrix.mul_apply,
    Matrix.of_apply, WithLp.ofLp_toLp]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  conv_rhs => rw [← hh]
  simp

lemma purif_regroup {rho : Matrix (D × E) (D × E) ℂ} {psi : (D × E) × X → ℂ}
    (h : UnnormalizedPurifies psi rho) :
    UnnormalizedPurifies (fun p : D × (E × X) => psi ((p.1, p.2.1), p.2.2))
      (QAlgorithms.traceRight rho) := by
  unfold UnnormalizedPurifies at h ⊢
  rw [← h]
  ext i j
  simp [vectorOuterProduct, QAlgorithms.traceRight, QAlgorithms.pureDensity,
    Fintype.sum_prod_type]

lemma overlap_regroup (psi phi : (D × E) × X → ℂ) (U : Matrix X X ℂ) :
    ∑ x : (D × E) × X, conj (psi x) * ∑ r : X, U x.2 r * phi (x.1, r) =
      ∑ x : D × (E × X), conj (psi ((x.1, x.2.1), x.2.2)) *
        ∑ r : E × X, ((1 : Matrix E E ℂ) ⊗ₖ U) x.2 r * phi ((x.1, r.1), r.2) := by
  simp only [Fintype.sum_prod_type, kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul,
    zero_mul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ =>
    Finset.sum_congr rfl fun r _ => ?_
  congr 1
  rw [Fintype.sum_eq_single e (fun b hb => by simp [Ne.symm hb])]
  simp

theorem fid_traceRight (rho sigma : Op (D × E)) (hrho : rho.PosSemidef)
    (hsigma : sigma.PosSemidef) :
    QAlgorithms.rootFidelity rho sigma ≤
      QAlgorithms.rootFidelity (QAlgorithms.traceRight rho) (QAlgorithms.traceRight sigma) := by
  have hp := purif_exists hrho
  have hq := purif_exists hsigma
  obtain ⟨U, hU⟩ := (uhlmann_greatest rho sigma hrho hsigma _ _ hp hq).1
  have hρ : (QAlgorithms.traceRight rho).PosSemidef := by
    rw [purif_eq (purif_regroup hp)]; exact Matrix.posSemidef_self_mul_conjTranspose _
  have hσ : (QAlgorithms.traceRight sigma).PosSemidef := by
    rw [purif_eq (purif_regroup hq)]; exact Matrix.posSemidef_self_mul_conjTranspose _
  have hK : ((1 : Matrix E E ℂ) ⊗ₖ (U : Matrix (D × E) (D × E) ℂ)) ∈ Matrix.unitaryGroup (E × (D × E)) ℂ :=
    kronecker_mem_unitary (one_mem _) U.2
  refine (uhlmann_greatest _ _ hρ hσ _ _ (purif_regroup hp) (purif_regroup hq)).2 ⟨⟨_, hK⟩, ?_⟩
  rw [hU]
  exact congrArg _ (overlap_regroup (fun p => cfc Real.sqrt rho p.1 p.2)
    (fun p => cfc Real.sqrt sigma p.1 p.2) U)

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

lemma purif_of (Ψ : Matrix I R ℂ) :
    UnnormalizedPurifies (fun p : I × R => Ψ p.1 p.2) (Ψ * Ψᴴ) := by
  unfold UnnormalizedPurifies
  ext i j
  simp [vectorOuterProduct, QAlgorithms.traceRight, QAlgorithms.pureDensity, Matrix.mul_apply]

theorem fid_isometry (V : Matrix J I ℂ) (hV : Vᴴ * V = 1) (rho sigma : Matrix I I ℂ)
    (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) :
    QAlgorithms.rootFidelity rho sigma ≤
      QAlgorithms.rootFidelity (V * rho * Vᴴ) (V * sigma * Vᴴ) := by
  have hp := purif_exists hrho
  have hq := purif_exists hsigma
  obtain ⟨U, hU⟩ := (uhlmann_greatest rho sigma hrho hsigma _ _ hp hq).1
  set a := cfc Real.sqrt rho
  set b := cfc Real.sqrt sigma
  have er : V * rho * Vᴴ = (V * a) * (V * a)ᴴ := by
    rw [conjTranspose_mul, X5B2.sqrt_herm, show V * a * (a * Vᴴ) = V * (a * a) * Vᴴ by
      simp only [Matrix.mul_assoc], X5B2.sqrt_sq hrho]
  have es : V * sigma * Vᴴ = (V * b) * (V * b)ᴴ := by
    rw [conjTranspose_mul, X5B2.sqrt_herm, show V * b * (b * Vᴴ) = V * (b * b) * Vᴴ by
      simp only [Matrix.mul_assoc], X5B2.sqrt_sq hsigma]
  have hp' := purif_of (V * a)
  have hq' := purif_of (V * b)
  rw [← er] at hp'
  rw [← es] at hq'
  refine (uhlmann_greatest _ _ (hrho.mul_mul_conjTranspose_same V)
    (hsigma.mul_mul_conjTranspose_same V) _ _ hp' hq').2 ⟨U, ?_⟩
  rw [hU]
  have h1 := overlap_eq (fun p : I × I => a p.1 p.2) (fun p => b p.1 p.2) (U : Matrix I I ℂ)
  have h2 := overlap_eq (fun p : J × I => (V * a) p.1 p.2) (fun p => (V * b) p.1 p.2)
    (U : Matrix I I ℂ)
  refine congrArg _ (h1.trans (Eq.trans ?_ h2.symm))
  show (aᴴ * b * _).trace = ((V * a)ᴴ * (V * b) * _).trace
  rw [conjTranspose_mul, show aᴴ * Vᴴ * (V * b) = aᴴ * (Vᴴ * V) * b by
    simp only [Matrix.mul_assoc], hV, Matrix.mul_one]

lemma stinespring {m : ℕ} (E : Fin m → Matrix J I ℂ) (rho : Matrix I I ℂ) :
    QAlgorithms.traceRight ((Matrix.of fun (p : J × Fin m) (i : I) => E p.2 p.1 i) * rho *
      (Matrix.of fun (p : J × Fin m) (i : I) => E p.2 p.1 i)ᴴ) = ∑ k, E k * rho * (E k)ᴴ := by
  ext j j'
  simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.mul_apply, conjTranspose_apply,
    Matrix.sum_apply]

lemma stinespring_iso {m : ℕ} (E : Fin m → Matrix J I ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) :
    (Matrix.of fun (p : J × Fin m) (i : I) => E p.2 p.1 i)ᴴ *
      (Matrix.of fun (p : J × Fin m) (i : I) => E p.2 p.1 i) = 1 := by
  rw [← hE]
  ext i i'
  simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, Matrix.sum_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

theorem fid_channel (rho sigma : Op I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (T : QAlgorithms.Superop I J) (hT : QAlgorithms.IsChannel T) :
    QAlgorithms.rootFidelity rho sigma ≤ QAlgorithms.rootFidelity (T rho) (T sigma) := by
  obtain ⟨m, E, hE, hTE⟩ := hT
  set V := Matrix.of fun (p : J × Fin m) (i : I) => E p.2 p.1 i
  have hV : Vᴴ * V = 1 := stinespring_iso E hE
  rw [hTE, hTE]
  show _ ≤ QAlgorithms.rootFidelity (∑ k, E k * rho * (E k)ᴴ) (∑ k, E k * sigma * (E k)ᴴ)
  rw [← stinespring E rho, ← stinespring E sigma]
  exact (fid_isometry V hV rho sigma hrho hsigma).trans
    (fid_traceRight _ _ (hrho.mul_mul_conjTranspose_same V) (hsigma.mul_mul_conjTranspose_same V))

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

lemma tr_psd {X : Matrix (D × E) (D × E) ℂ} (h : X.PosSemidef) :
    (QAlgorithms.traceRight X).PosSemidef := by
  rw [purif_eq (purif_regroup (purif_exists h))]
  exact Matrix.posSemidef_self_mul_conjTranspose _

lemma tr_add (X Y : Matrix (D × E) (D × E) ℂ) :
    QAlgorithms.traceRight (X + Y) = QAlgorithms.traceRight X + QAlgorithms.traceRight Y := by
  ext i j; simp [QAlgorithms.traceRight, Finset.sum_add_distrib]

lemma tr_sub (X Y : Matrix (D × E) (D × E) ℂ) :
    QAlgorithms.traceRight (X - Y) = QAlgorithms.traceRight X - QAlgorithms.traceRight Y := by
  ext i j; simp [QAlgorithms.traceRight, Finset.sum_sub_distrib]

lemma tr_sum {K : Type*} [Fintype K] (X : K → Matrix (D × E) (D × E) ℂ) :
    QAlgorithms.traceRight (∑ k, X k) = ∑ k, QAlgorithms.traceRight (X k) := by
  ext i j; simp [QAlgorithms.traceRight, Matrix.sum_apply]; rw [Finset.sum_comm]

lemma kl_apply (A : Matrix E E ℂ) (X : Matrix (D × E) (D × E) ℂ) (d : D) (e : E) (q : D × E) :
    (((1 : Matrix D D ℂ) ⊗ₖ A) * X) (d, e) q = ∑ i, A e i * X (d, i) q := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, ite_mul]

lemma kr_apply (B : Matrix E E ℂ) (X : Matrix (D × E) (D × E) ℂ) (p : D × E) (d : D) (e : E) :
    (X * ((1 : Matrix D D ℂ) ⊗ₖ B)) p (d, e) = ∑ i, X p (d, i) * B i e := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, mul_ite]

lemma tr_cyc (A B : Matrix E E ℂ) (X : Matrix (D × E) (D × E) ℂ) :
    QAlgorithms.traceRight (((1 : Matrix D D ℂ) ⊗ₖ A) * X * ((1 : Matrix D D ℂ) ⊗ₖ B)) =
      QAlgorithms.traceRight (((1 : Matrix D D ℂ) ⊗ₖ (B * A)) * X) := by
  ext d d'
  simp only [QAlgorithms.traceRight, Matrix.of_apply]
  simp only [kr_apply]
  simp only [kl_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun e _ => ?_
  ring

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

open scoped Matrix.Norms.L2Operator in
lemma sqrt_mono {A B : Matrix E E ℂ} (hA : A.PosSemidef) (hAB : (B - A).PosSemidef) :
    (cfc Real.sqrt B - cfc Real.sqrt A).PosSemidef := by
  have hA0 : (0 : Matrix E E ℂ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hle : A ≤ B := Matrix.le_iff.mpr hAB
  have hB0 : (0 : Matrix E E ℂ) ≤ B := hA0.trans hle
  have h := CFC.sqrt_le_sqrt A B hle
  rw [CFC.sqrt_eq_real_sqrt A hA0, CFC.sqrt_eq_real_sqrt B hB0,
    cfcₙ_eq_cfc (by exact (A.finite_real_spectrum.union (Set.finite_singleton 0)).continuousOn _ |>.mono (by rw [quasispectrum_eq_spectrum_union_zero])) (by simp),
    cfcₙ_eq_cfc (by exact (B.finite_real_spectrum.union (Set.finite_singleton 0)).continuousOn _ |>.mono (by rw [quasispectrum_eq_spectrum_union_zero])) (by simp)] at h
  exact Matrix.le_iff.mp h

lemma fid_mono_right {rho s1 s2 : Matrix E E ℂ} (hrho : rho.PosSemidef) (h1 : s1.PosSemidef)
    (h12 : (s2 - s1).PosSemidef) :
    QAlgorithms.rootFidelity rho s1 ≤ QAlgorithms.rootFidelity rho s2 := by
  unfold QAlgorithms.rootFidelity
  set a := cfc Real.sqrt rho
  have ha : aᴴ = a := X5B2.sqrt_herm rho
  have hc : ∀ X : Matrix E E ℂ, X.PosSemidef → (a * X * a).PosSemidef := by
    intro X hX
    have := hX.mul_mul_conjTranspose_same a
    rwa [ha] at this
  have hd : (a * s2 * a - a * s1 * a).PosSemidef := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]; exact hc _ h12
  have := X5B2.psd_re (sqrt_mono (hc _ h1) hd)
  rw [Matrix.trace_sub, Complex.sub_re] at this
  linarith

lemma kraus_tensor {m : ℕ} (W : QAlgorithms.Superop E E) (K : Fin m → Matrix E E ℂ)
    (hK : ∀ X, W X = QAlgorithms.krausApply K X) (sigma : Matrix (D × E) (D × E) ℂ) :
    QAlgorithms.idTensorSuperop W sigma =
      ∑ k, ((1 : Matrix D D ℂ) ⊗ₖ K k) * sigma * ((1 : Matrix D D ℂ) ⊗ₖ (K k)ᴴ) := by
  ext ⟨d, e⟩ ⟨d', e'⟩
  simp only [QAlgorithms.idTensorSuperop, Matrix.of_apply, hK, QAlgorithms.krausApply,
    Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [kr_apply]
  simp only [kl_apply]
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]

lemma tr_vmv (A : Matrix E E ℂ) (x : E → ℂ) :
    (A * vecMulVec x (star x)).trace = star x ⬝ᵥ (A *ᵥ x) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct,
    mulVec, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply]; ring

lemma tni_psd {m : ℕ} (W : QAlgorithms.Superop E E) (K : Fin m → Matrix E E ℂ)
    (hK : ∀ X, W X = QAlgorithms.krausApply K X)
    (htr : ∀ X : Op E, X.PosSemidef → (W X).trace.re ≤ X.trace.re) :
    (1 - ∑ k, (K k)ᴴ * K k).PosSemidef := by
  have hH : (1 - ∑ k, (K k)ᴴ * K k).IsHermitian :=
    isHermitian_one.sub (Matrix.posSemidef_sum _ fun k _ =>
      Matrix.posSemidef_conjTranspose_mul_self (K k)).1
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
  have h := htr _ (Matrix.posSemidef_vecMulVec_self_star x)
  have e1 : (W (vecMulVec x (star x))).trace = star x ⬝ᵥ ((∑ k, (K k)ᴴ * K k) *ᵥ x) := by
    rw [hK, QAlgorithms.krausApply, Matrix.trace_sum, ← tr_vmv, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
  have e2 : (vecMulVec x (star x)).trace = star x ⬝ᵥ ((1 : Matrix E E ℂ) *ᵥ x) := by
    rw [← tr_vmv, Matrix.one_mul]
  rw [e1, e2] at h
  rw [Complex.nonneg_iff]
  refine ⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
  linarith

lemma kt (A : Matrix E E ℂ) : ((1 : Matrix D D ℂ) ⊗ₖ A)ᴴ = (1 : Matrix D D ℂ) ⊗ₖ Aᴴ := by
  rw [conjTranspose_kronecker, conjTranspose_one]

lemma trK_apply (A : Matrix E E ℂ) (X : Matrix (D × E) (D × E) ℂ) (d d' : D) :
    QAlgorithms.traceRight (((1 : Matrix D D ℂ) ⊗ₖ A) * X) d d' =
      ∑ e, ∑ i, A e i * X (d, i) (d', e) := by
  simp only [QAlgorithms.traceRight, Matrix.of_apply, kl_apply]

theorem fid_tni (rho sigma : Op (D × E)) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (W : QAlgorithms.Superop E E) (hW : TNI W) :
    QAlgorithms.rootFidelity rho (QAlgorithms.idTensorSuperop W sigma) ≤
      QAlgorithms.rootFidelity (QAlgorithms.traceRight rho) (QAlgorithms.traceRight sigma) := by
  obtain ⟨⟨m, K, hK⟩, htr⟩ := hW
  have hN := tni_psd W K hK htr
  rw [kraus_tensor W K hK sigma]
  set Y := ∑ k, ((1 : Matrix D D ℂ) ⊗ₖ K k) * sigma * ((1 : Matrix D D ℂ) ⊗ₖ (K k)ᴴ)
  have hY : Y.PosSemidef := by
    refine Matrix.posSemidef_sum _ fun k _ => ?_
    have := hsigma.mul_mul_conjTranspose_same ((1 : Matrix D D ℂ) ⊗ₖ K k)
    rwa [kt] at this
  refine (fid_traceRight rho Y hrho hY).trans (fid_mono_right (tr_psd hrho) (tr_psd hY) ?_)
  set N := 1 - ∑ k, (K k)ᴴ * K k
  set r := cfc Real.sqrt N
  have hr : rᴴ = r := X5B2.sqrt_herm N
  have hrr : r * r = N := X5B2.sqrt_sq hN
  have key : QAlgorithms.traceRight sigma - QAlgorithms.traceRight Y =
      QAlgorithms.traceRight (((1 : Matrix D D ℂ) ⊗ₖ r) * sigma * ((1 : Matrix D D ℂ) ⊗ₖ r)) := by
    rw [tr_cyc, hrr, tr_sum]
    simp only [tr_cyc]
    ext d d'
    simp only [Matrix.sub_apply, Matrix.sum_apply, trK_apply, N, Matrix.one_apply, Matrix.sum_apply,
      sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    congr 1
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun e _ => ?_)
    exact Finset.sum_comm
  rw [key]
  refine tr_psd ?_
  have := hsigma.mul_mul_conjTranspose_same ((1 : Matrix D D ℂ) ⊗ₖ r)
  rwa [kt, hr] at this

end X5UH
end X5mod_UH_B8

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Information100.P32 (Op)

theorem solution {D E : Type*} [Fintype D] [Fintype E]
    [DecidableEq D] [DecidableEq E] [Nonempty D] [Nonempty E]
    (rho sigma : Op (D × E)) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (W : QAlgorithms.Superop E E) (hW : TNI W) :
    QAlgorithms.rootFidelity rho (QAlgorithms.idTensorSuperop W sigma) ≤
      QAlgorithms.rootFidelity (QAlgorithms.traceRight rho) (QAlgorithms.traceRight sigma) :=
  X5UH.fid_tni rho sigma hrho hsigma W hW

end
