-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:15:06.991555+00:00
-- url     : https://prove2.me/submissions/326a8c9b-d6fc-4e32-89a8-fceff70eaded

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


noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Information100.P32 (Op)

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Op I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (htrace : 0 < rho.trace.re) :
    negLogBits (ENNReal.ofReal ((QAlgorithms.rootFidelity rho sigma / rho.trace.re) ^ 2)) ≤
      normalizedRelativeEntropyBits rho sigma :=
  X5B2.main rho sigma hrho hsigma htrace

end
