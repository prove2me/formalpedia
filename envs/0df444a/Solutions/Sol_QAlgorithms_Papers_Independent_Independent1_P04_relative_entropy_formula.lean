-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.relative_entropy_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:49:33.821999+00:00
-- url     : https://prove2.me/submissions/627bd8ac-a564-41e3-95ed-bc8b68444cb2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_backgroundSSA
import Theorems.Thm_QAlgorithms_Arunachalam_vnEntropy_subadditive
import Theorems.Thm_SimpleSSA_Monotone_eq_4
import Theorems.Thm_BanditAlgorithm_bernoulli_relative_entropy_pinsker
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
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

theorem x5ai_finite_cont' {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ M) :=
  M.finite_real_spectrum.continuousOn _

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

/-- identity tensor X as a star algebra hom -/
noncomputable def x5ai_kronHom (C : Type*) {n : Type*} [Fintype C] [DecidableEq C] [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (C × n) (C × n) ℂ where
  toFun X := Matrix.kronecker (1 : Matrix C C ℂ) X
  map_one' := Matrix.one_kronecker_one
  map_mul' X Y := by
    have := Matrix.mul_kronecker_mul (1 : Matrix C C ℂ) (1 : Matrix C C ℂ) X Y
    rw [Matrix.mul_one] at this
    exact this
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.kronecker_add]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> simp_all
  map_star' X := by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]

theorem x5ai_kron (C : Type*) {n : Type*} [Fintype C] [DecidableEq C] [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.kronecker (1 : Matrix C C ℂ) M) = Matrix.kronecker (1 : Matrix C C ℂ) (cfc f M) := by
  have hK : (Matrix.kronecker (1 : Matrix C C ℂ) M).IsHermitian := by
    simp [IsHermitian, Matrix.conjTranspose_kronecker, hM.eq]
  have h := StarAlgHom.map_cfc (R := ℝ) (S := ℂ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (x5ai_kronHom C (n := n)) f M (x5ai_finite_cont' M f)
    (by
      change Continuous fun X : Matrix n n ℂ => Matrix.kronecker (1 : Matrix C C ℂ) X
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
      exact continuous_const.mul ((continuous_apply _).comp (continuous_apply _)))
    hM.isSelfAdjoint hK.isSelfAdjoint
  exact h.symm

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

theorem cfc_kron {X : Matrix ι ι ℂ} {Y : Matrix κ κ ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (f : ℝ → ℝ) (hf0 : f 0 = 0) (hmul : ∀ x y, 0 ≤ x → 0 ≤ y → f (x * y) = f x * f y) :
    cfc f (X ⊗ₖ Y) = cfc f X ⊗ₖ cfc f Y := by
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
    cfc_spec hXh, cfc_spec hYh]
  have hd : ∀ k, 0 ≤ d k := hX.eigenvalues_nonneg
  have he : ∀ k, 0 ≤ e k := hY.eigenvalues_nonneg
  have hDE' : diagonal (fun p : ι × κ => ((f (d p.1 * e p.2) : ℝ) : ℂ)) =
      diagonal (fun k => ((f (d k) : ℝ) : ℂ)) ⊗ₖ diagonal (fun k => ((f (e k) : ℝ) : ℂ)) := by
    rw [diagonal_kronecker_diagonal]; congr 1; ext p
    simp [hmul _ _ (hd p.1) (he p.2)]
  rw [hDE', conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

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

lemma OEmb.pow (hE : OEmb E) (Y : K → Matrix m m ℂ) (k : ℕ) :
    (∑ b, E b (Y b)) ^ (k + 1) = ∑ b, E b (Y b ^ (k + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single b (fun c _ hc => by rw [hE.mul, if_neg (Ne.symm hc)])
      (by simp), hE.mul, if_pos rfl, ← pow_succ]

lemma OEmb.aeval (hE : OEmb E) (Y : K → Matrix m m ℂ) (p : ℝ[X]) (hp : p.coeff 0 = 0) :
    aeval (∑ b, E b (Y b)) p = ∑ b, E b (aeval (Y b) p) := by
  simp only [aeval_eq_sum_range, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases i with _ | k
  · simp [hp]
  · rw [hE.pow, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [LinearMap.map_smul_of_tower]

lemma OEmb.herm (hE : OEmb E) {Y : K → Matrix m m ℂ} (hY : ∀ b, (Y b).IsHermitian) :
    (∑ b, E b (Y b)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hE.star, (hY b).eq]

theorem OEmb.cfc_sum (hE : OEmb E) {Y : K → Matrix m m ℂ} (hY : ∀ b, (Y b).IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) :
    cfc f (∑ b, E b (Y b)) = ∑ b, E b (cfc f (Y b)) := by
  set X := ∑ b, E b (Y b)
  have hX : IsSelfAdjoint X := (hE.herm hY).isSelfAdjoint
  have fX : (spectrum ℝ X).Finite := X.finite_real_spectrum
  have fY : ∀ b, (spectrum ℝ (Y b)).Finite := fun b => (Y b).finite_real_spectrum
  set s : Finset ℝ := {0} ∪ fX.toFinset ∪ Finset.univ.biUnion (fun b => (fY b).toFinset)
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have h1 : cfc f X = cfc (fun x => p.eval x) X :=
    cfc_congr fun x hx => (hp x (by simp [s, fX.mem_toFinset.2 hx])).symm
  have h2 : ∀ b, cfc f (Y b) = cfc (fun x => p.eval x) (Y b) := fun b =>
    cfc_congr fun x hx => (hp x (by
      simp only [s, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact Or.inr ⟨b, (fY b).mem_toFinset.2 hx⟩)).symm
  rw [h1, cfc_polynomial p X hX]
  simp only [h2]
  rw [Finset.sum_congr rfl fun b _ => by rw [cfc_polynomial p (Y b) (hY b).isSelfAdjoint]]
  refine hE.aeval Y p ?_
  rw [Polynomial.coeff_zero_eq_eval_zero, hp 0 (by simp [s]), hf]

end X5QC

namespace X5QC
set_option linter.unusedSectionVars false
variable {m n B : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype B]
  [DecidableEq B]

/-- rank-one projector on the `b`-th column of `U`. -/
noncomputable def proj (U : Matrix B B ℂ) (b : B) : Matrix B B ℂ :=
  vecMulVec (fun β => U β b) (star fun β => U β b)

lemma proj_mul {U : Matrix B B ℂ} (hU : Uᴴ * U = 1) (b c : B) :
    proj U b * proj U c = if b = c then proj U b else 0 := by
  have h : ∀ b c, (star fun β => U β b) ⬝ᵥ (fun β => U β c) = if b = c then 1 else 0 := by
    intro b c
    have := congrFun (congrFun hU b) c
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply] at this
    rw [← this]; rfl
  unfold proj
  rw [vecMulVec_mul_vecMulVec, h]
  split_ifs with hbc
  · subst hbc; simp
  · simp

lemma proj_star (U : Matrix B B ℂ) (b : B) : (proj U b)ᴴ = proj U b := by
  unfold proj
  ext i j; simp [vecMulVec_apply, mul_comm]

lemma proj_trace {U : Matrix B B ℂ} (hU : Uᴴ * U = 1) (b : B) : (proj U b).trace = 1 := by
  have := congrFun (congrFun hU b) b
  simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply, if_true] at this
  rw [← this]
  simp [proj, Matrix.trace, vecMulVec_apply, mul_comm]

/-- `Y ↦ e (Y ⊗ |u_b⟩⟨u_b|)`. -/
noncomputable def emb (e : m × B ≃ n) (U : Matrix B B ℂ) (b : B) :
    Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun Y := (Y ⊗ₖ proj U b).submatrix e.symm e.symm
  map_add' Y Z := by rw [add_kronecker]; rfl
  map_smul' c Y := by rw [smul_kronecker]; rfl

lemma emb_apply (e : m × B ≃ n) (U : Matrix B B ℂ) (b : B) (Y : Matrix m m ℂ) (x y : n) :
    emb e U b Y x y = Y (e.symm x).1 (e.symm y).1 *
      (U (e.symm x).2 b * conj (U (e.symm y).2 b)) := by
  simp [emb, proj, vecMulVec_apply, kroneckerMap_apply]

lemma emb_oemb (e : m × B ≃ n) {U : Matrix B B ℂ} (hU : Uᴴ * U = 1) : OEmb (emb e U) where
  mul b c Y Z := by
    simp only [emb, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Matrix.submatrix_mul_equiv, ← mul_kronecker_mul, proj_mul hU]
    split_ifs <;> simp
  star b Y := by
    simp only [emb, LinearMap.coe_mk, AddHom.coe_mk]
    rw [conjTranspose_submatrix, conjTranspose_kronecker, proj_star]

lemma emb_trace (e : m × B ≃ n) {U : Matrix B B ℂ} (hU : Uᴴ * U = 1) (b : B) (Y : Matrix m m ℂ) :
    (emb e U b Y).trace = Y.trace := by
  simp only [emb, LinearMap.coe_mk, AddHom.coe_mk]
  have : ((Y ⊗ₖ proj U b).submatrix e.symm e.symm).trace = (Y ⊗ₖ proj U b).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact Equiv.sum_comp e.symm (fun i => (Y ⊗ₖ proj U b) i i)
  rw [this, trace_kronecker, proj_trace hU, mul_one]

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

lemma ind_zero : ind 0 = 0 := by simp [ind]

lemma supp_herm (X : Matrix ι ι ℂ) : (supp X)ᴴ = supp X :=
  (cfc_predicate ind X : IsSelfAdjoint _)

lemma mul_supp {X : Matrix ι ι ℂ} (hX : X.IsHermitian) : X * supp X = X := by
  unfold supp
  nth_rewrite 1 [← cfc_id' ℝ X hX.isSelfAdjoint]
  rw [← cfc_mul _ _ _ (X5B2.fin _ _) (X5B2.fin _ _)]
  conv_rhs => rw [← cfc_id' ℝ X hX.isSelfAdjoint]
  refine cfc_congr fun x _ => ?_
  by_cases h : x = 0 <;> simp [ind, h]

lemma supp_mul {X : Matrix ι ι ℂ} (hX : X.IsHermitian) : supp X * X = X := by
  have := congrArg conjTranspose (mul_supp hX)
  rwa [conjTranspose_mul, supp_herm, hX.eq] at this

lemma supp_idem (X : Matrix ι ι ℂ) : supp X * supp X = supp X := by
  unfold supp
  rw [← cfc_mul _ _ _ (X5B2.fin _ _) (X5B2.fin _ _)]
  refine cfc_congr fun x _ => ?_
  by_cases h : x = 0 <;> simp [ind, h]

lemma supp_eq_inv_mul (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    supp X = cfc (fun x : ℝ => x⁻¹) X * X := by
  unfold supp
  conv_rhs => arg 2; rw [← cfc_id' ℝ X hX.isSelfAdjoint]
  rw [← cfc_mul _ _ _ (X5B2.fin _ _) (X5B2.fin _ _)]
  refine cfc_congr fun x _ => ?_
  by_cases h : x = 0 <;> simp [ind, h]

lemma isSupported_of {rho sigma : Matrix ι ι ℂ} (hs : sigma.IsHermitian)
    (h : rho * supp sigma = rho) :
    QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported rho sigma := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  rw [← h, ← Matrix.mulVec_mulVec, supp_eq_inv_mul sigma hs, ← Matrix.mulVec_mulVec, hv]
  simp

lemma kq_apply (X : Matrix (ι × κ) (ι × κ) ℂ) (Q : Matrix ι ι ℂ) (p : ι × κ) (i : ι) (k : κ) :
    (X * (Q ⊗ₖ (1 : Matrix κ κ ℂ))) p (i, k) = ∑ j, X p (j, k) * Q j i := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, mul_ite]

lemma tr_kron_one_right (X : Matrix (ι × κ) (ι × κ) ℂ) (Q : Matrix ι ι ℂ) :
    (X * (Q ⊗ₖ (1 : Matrix κ κ ℂ))).trace = (QAlgorithms.traceRight X * Q).trace := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
  simp only [kq_apply]
  simp only [Matrix.mul_apply, QAlgorithms.traceRight, Matrix.of_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

lemma tr_one_kron_right (X : Matrix (ι × κ) (ι × κ) ℂ) (Q : Matrix κ κ ℂ) :
    (X * ((1 : Matrix ι ι ℂ) ⊗ₖ Q)).trace = (QAlgorithms.traceLeft X * Q).trace := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
  simp only [X5UH.kr_apply]
  simp only [Matrix.mul_apply, QAlgorithms.traceLeft, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]

/-- If `M X M = 0`-type trace vanishes then `X M = 0`. -/
lemma mul_eq_zero_of_tr {X M : Matrix ι ι ℂ} (hX : X.PosSemidef) (hM : Mᴴ = M) (hMM : M * M = M)
    (htr : (X * M).trace = 0) : X * M = 0 := by
  set s := cfc Real.sqrt X
  have hs : sᴴ = s := X5B2.sqrt_herm X
  have hss : s * s = X := X5B2.sqrt_sq hX
  have h1 : (s * M)ᴴ * (s * M) = M * X * M := by
    rw [conjTranspose_mul, hs, hM, ← hss]; simp only [Matrix.mul_assoc]
  have h2 : (M * X * M).PosSemidef := by
    have := hX.mul_mul_conjTranspose_same M; rwa [hM] at this
  have h3 : (M * X * M).trace = 0 := by
    rw [Matrix.trace_mul_cycle, hMM, Matrix.trace_mul_comm, htr]
  have h4 : s * M = 0 := by
    rw [← Matrix.conjTranspose_mul_self_eq_zero, h1]
    exact h2.trace_eq_zero_iff.mp h3
  rw [← hss, Matrix.mul_assoc, h4, Matrix.mul_zero]

lemma supp_marg_left {X : Matrix (ι × κ) (ι × κ) ℂ} (hX : X.PosSemidef) :
    X * (supp (QAlgorithms.traceRight X) ⊗ₖ (1 : Matrix κ κ ℂ)) = X := by
  set R := QAlgorithms.traceRight X
  have hR : R.IsHermitian := (X5UH.tr_psd hX).1
  set Q := 1 - supp R
  have hQ : Qᴴ = Q := by simp [Q, supp_herm]
  have hQQ : Q * Q = Q := by
    simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, supp_idem]; abel
  have hRQ : R * Q = 0 := by simp [Q, Matrix.mul_sub, mul_supp hR]
  set M := Q ⊗ₖ (1 : Matrix κ κ ℂ)
  have hM : Mᴴ = M := by simp [M, conjTranspose_kronecker, hQ]
  have hMM : M * M = M := by simp [M, ← mul_kronecker_mul, hQQ]
  have h := mul_eq_zero_of_tr hX hM hMM (by rw [tr_kron_one_right, hRQ, Matrix.trace_zero])
  have e : supp R ⊗ₖ (1 : Matrix κ κ ℂ) = 1 - M := by
    refine eq_sub_of_add_eq ?_
    rw [← add_kronecker, show supp R + Q = 1 by simp [Q], one_kronecker_one]
  rw [e, Matrix.mul_sub, h, Matrix.mul_one, sub_zero]

lemma supp_marg_right {X : Matrix (ι × κ) (ι × κ) ℂ} (hX : X.PosSemidef) :
    X * ((1 : Matrix ι ι ℂ) ⊗ₖ supp (QAlgorithms.traceLeft X)) = X := by
  set R := QAlgorithms.traceLeft X
  have hR : R.IsHermitian := by
    ext i j
    simp only [R, conjTranspose_apply, QAlgorithms.traceLeft, Matrix.of_apply, star_sum]
    exact Finset.sum_congr rfl fun a _ => hX.1.apply _ _
  set Q := 1 - supp R
  have hQ : Qᴴ = Q := by simp [Q, supp_herm]
  have hQQ : Q * Q = Q := by
    simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, supp_idem]; abel
  have hRQ : R * Q = 0 := by simp [Q, Matrix.mul_sub, mul_supp hR]
  set M := (1 : Matrix ι ι ℂ) ⊗ₖ Q
  have hM : Mᴴ = M := by simp [M, conjTranspose_kronecker, hQ]
  have hMM : M * M = M := by simp [M, ← mul_kronecker_mul, hQQ]
  have h := mul_eq_zero_of_tr hX hM hMM (by rw [tr_one_kron_right, hRQ, Matrix.trace_zero])
  have e : (1 : Matrix ι ι ℂ) ⊗ₖ supp R = 1 - M := by
    refine eq_sub_of_add_eq ?_
    rw [← kronecker_add, show supp R + Q = 1 by simp [Q], one_kronecker_one]
  rw [e, Matrix.mul_sub, h, Matrix.mul_one, sub_zero]

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

def e1 (A B C : Type*) : (A × C) × B ≃ A × (B × C) where
  toFun x := (x.1.1, (x.2, x.1.2))
  invFun y := ((y.1, y.2.2), y.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

variable (U : Matrix B B ℂ) (p : B → ℝ) (rho : B → Matrix (A × C) (A × C) ℂ)

lemma qcq_eq : qcq U p rho = ∑ b, emb (e1 A B C) U b ((p b : ℂ) • rho b) := by
  ext x y
  simp only [qcq, Matrix.sum_apply, emb_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [e1, Equiv.coe_fn_symm_mk]; ring

lemma rec_eq : qcqRecovered U p rho = ∑ b, emb (e1 A B C) U b
    ((p b : ℂ) • (QAlgorithms.traceRight (rho b) ⊗ₖ QAlgorithms.traceLeft (rho b))) := by
  ext x y
  simp only [qcqRecovered, Matrix.sum_apply, emb_apply, Matrix.smul_apply, smul_eq_mul,
    kroneckerMap_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [e1, Equiv.coe_fn_symm_mk]; ring

lemma ab_eq : marginalAB (qcq U p rho) = ∑ b, emb (Equiv.refl (A × B)) U b
    ((p b : ℂ) • QAlgorithms.traceRight (rho b)) := by
  ext x y
  simp only [marginalAB, qcq, Matrix.sum_apply, emb_apply, Matrix.smul_apply, smul_eq_mul,
    QAlgorithms.traceRight, Matrix.of_apply, Equiv.refl_symm, Equiv.refl_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

lemma bc_eq : QAlgorithms.traceLeft (qcq U p rho) = ∑ b, emb (Equiv.prodComm C B) U b
    ((p b : ℂ) • QAlgorithms.traceLeft (rho b)) := by
  ext x y
  simp only [qcq, Matrix.sum_apply, emb_apply, Matrix.smul_apply, smul_eq_mul,
    QAlgorithms.traceLeft, Matrix.of_apply, Equiv.prodComm_symm, Equiv.prodComm_apply,
    Prod.fst_swap, Prod.snd_swap, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

lemma b_eq (htr : ∀ b, (rho b).trace = 1) :
    QAlgorithms.traceRight (QAlgorithms.traceLeft (qcq U p rho)) =
      ∑ b, emb (Equiv.punitProd B : Unit × B ≃ B) U b ((p b : ℂ) • (1 : Matrix Unit Unit ℂ)) := by
  ext x y
  simp only [qcq, Matrix.sum_apply, emb_apply, Matrix.smul_apply, smul_eq_mul,
    QAlgorithms.traceLeft, QAlgorithms.traceRight, Matrix.of_apply, Equiv.punitProd_symm_apply,
    Matrix.one_apply_eq, mul_one]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := htr b
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type] at h
  simp_rw [← Finset.mul_sum]
  rw [h]; ring

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

lemma cfc_xlogx_smul {p : ℝ} (hp : 0 ≤ p) (Y : Matrix ι ι ℂ) (hY : Y.IsHermitian) :
    cfc (fun x : ℝ => x * Real.log x) ((p : ℂ) • Y) =
      (p : ℂ) • cfc (fun x : ℝ => x * Real.log x) Y + ((p * Real.log p : ℝ) : ℂ) • Y := by
  rw [real_smul, ← cfc_comp_smul p _ Y ((Y.finite_real_spectrum.image _).continuousOn _) hY.isSelfAdjoint]
  rw [real_smul, real_smul]
  conv_rhs => arg 2; rw [← cfc_id' ℝ Y hY.isSelfAdjoint]
  rw [← cfc_smul _ _ _ (X5B2.fin _ _), ← cfc_smul _ _ _ (X5B2.fin _ _),
    ← cfc_add _ _ _ (X5B2.fin _ _) (X5B2.fin _ _)]
  refine cfc_congr fun x _ => ?_
  simp only [smul_eq_mul]
  rcases hp.eq_or_lt with h | h
  · subst h; simp
  by_cases hx : x = 0
  · subst hx; simp
  rw [Real.log_mul h.ne' hx]; ring

lemma cfc_log_smul {p : ℝ} (hp : 0 < p) (Y : Matrix ι ι ℂ) (hY : Y.IsHermitian) :
    cfc Real.log ((p : ℂ) • Y) = ((Real.log p : ℝ) : ℂ) • supp Y + cfc Real.log Y := by
  rw [real_smul, ← cfc_comp_smul p _ Y ((Y.finite_real_spectrum.image _).continuousOn _) hY.isSelfAdjoint, real_smul, supp,
    ← cfc_smul _ _ _ (X5B2.fin _ _), ← cfc_add _ _ _ (X5B2.fin _ _) (X5B2.fin _ _)]
  refine cfc_congr fun x _ => ?_
  simp only [smul_eq_mul, ind]
  by_cases hx : x = 0
  · subst hx; simp
  rw [if_neg hx, Real.log_mul hp.ne' hx]; ring

lemma supp_smul {p : ℝ} (hp : 0 < p) (Y : Matrix ι ι ℂ) (hY : Y.IsHermitian) :
    supp ((p : ℂ) • Y) = supp Y := by
  rw [supp, real_smul, ← cfc_comp_smul p _ Y ((Y.finite_real_spectrum.image _).continuousOn _) hY.isSelfAdjoint, supp]
  refine cfc_congr fun x _ => ?_
  simp [ind, hp.ne']

lemma supp_kron {Y : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ} (hY : Y.PosSemidef) (hZ : Z.PosSemidef) :
    supp (Y ⊗ₖ Z) = supp Y ⊗ₖ supp Z :=
  X5AD.cfc_kron hY hZ ind ind_zero (fun x y _ _ => by
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [ind, hx, hy])

lemma log_kron {Y : Matrix ι ι ℂ} {Z : Matrix κ κ ℂ} (hY : Y.PosSemidef) (hZ : Z.PosSemidef) :
    cfc Real.log (Y ⊗ₖ Z) = cfc Real.log Y ⊗ₖ supp Z + supp Y ⊗ₖ cfc Real.log Z :=
  cfc_kron2 hY hZ Real.log Real.log ind ind Real.log Real.log_zero (fun x y _ _ => by
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [ind, hx, hy, Real.log_mul])

/-- `Tr (X log X)`, in nats. -/
noncomputable def T (X : Matrix ι ι ℂ) : ℝ := (cfc (fun x : ℝ => x * Real.log x) X).trace.re

lemma T_smul {p : ℝ} (hp : 0 ≤ p) {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) (htr : Y.trace = 1) :
    T ((p : ℂ) • Y) = p * T Y + p * Real.log p := by
  unfold T
  rw [cfc_xlogx_smul hp Y hY, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, htr]
  simp [Complex.mul_re]

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

lemma OEmb.sum_mul_sum (hE : OEmb E) (Y Z : K → Matrix m m ℂ) :
    (∑ b, E b (Y b)) * (∑ c, E c (Z c)) = ∑ b, E b (Y b * Z b) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single b (fun c _ hc => by rw [hE.mul, if_neg (Ne.symm hc)])
    (by simp), hE.mul, if_pos rfl]

lemma OEmb.T_sum (hE : OEmb E) (htr : ∀ b Y, (E b Y).trace = Y.trace) {Y : K → Matrix m m ℂ}
    (hY : ∀ b, (Y b).IsHermitian) : T (∑ b, E b (Y b)) = ∑ b, T (Y b) := by
  unfold T
  rw [hE.cfc_sum hY _ (by simp), Matrix.trace_sum, Complex.re_sum]
  simp only [htr]
end gen

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma tr_traceRight (X : Matrix (ι × κ) (ι × κ) ℂ) : (QAlgorithms.traceRight X).trace = X.trace := by
  simp [Matrix.trace, QAlgorithms.traceRight, Fintype.sum_prod_type]

lemma tr_traceLeft (X : Matrix (ι × κ) (ι × κ) ℂ) : (QAlgorithms.traceLeft X).trace = X.trace := by
  simp [Matrix.trace, QAlgorithms.traceLeft, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

lemma tl_psd {X : Matrix (ι × κ) (ι × κ) ℂ} (hX : X.PosSemidef) :
    (QAlgorithms.traceLeft X).PosSemidef := by
  have h := X5UH.tr_psd (hX.submatrix (Equiv.prodComm κ ι))
  convert h using 1
  ext i j; simp [QAlgorithms.traceLeft, QAlgorithms.traceRight]

lemma herm_smul {p : ℝ} {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) : ((p : ℂ) • Y).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_smul, hY.eq]
  simp [Complex.star_def, Complex.conj_ofReal]

lemma T_one : T (1 : Matrix Unit Unit ℂ) = 0 := by
  unfold T
  rw [show (1 : Matrix Unit Unit ℂ) = algebraMap ℝ _ 1 by simp, cfc_algebraMap]
  simp

lemma mul_log (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    X * cfc Real.log X = cfc (fun x : ℝ => x * Real.log x) X := by
  nth_rewrite 1 [← cfc_id' ℝ X hX.isSelfAdjoint]
  rw [← cfc_mul _ _ _ (X5B2.fin _ _) (X5B2.fin _ _)]

/-- The log term for a single block. -/
lemma block_log {X : Matrix (ι × κ) (ι × κ) ℂ} (hX : X.PosSemidef) (htr : X.trace = 1)
    {p : ℝ} (hp : 0 ≤ p) :
    (((p : ℂ) • X) * cfc Real.log ((p : ℂ) •
      (QAlgorithms.traceRight X ⊗ₖ QAlgorithms.traceLeft X))).trace.re =
      p * (Real.log p + T (QAlgorithms.traceRight X) + T (QAlgorithms.traceLeft X)) := by
  rcases hp.eq_or_lt with h | h
  · subst h; simp
  set RA := QAlgorithms.traceRight X
  set RC := QAlgorithms.traceLeft X
  have hA : RA.PosSemidef := X5UH.tr_psd hX
  have hC : RC.PosSemidef := tl_psd hX
  have hS := hA.kronecker hC
  have h1 : X * (supp RA ⊗ₖ (1 : Matrix κ κ ℂ)) = X := supp_marg_left hX
  have h2 : X * ((1 : Matrix ι ι ℂ) ⊗ₖ supp RC) = X := supp_marg_right hX
  have h2' : ((1 : Matrix ι ι ℂ) ⊗ₖ supp RC) * X = X := by
    have := congrArg conjTranspose h2
    rwa [conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one, supp_herm, hX.1.eq] at this
  rw [cfc_log_smul h _ hS.1, supp_kron hA hC, log_kron hA hC]
  simp only [Matrix.smul_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_add]
  have e1 : (X * (supp RA ⊗ₖ supp RC)).trace = 1 := by
    rw [show supp RA ⊗ₖ supp RC = (supp RA ⊗ₖ (1 : Matrix κ κ ℂ)) * ((1 : Matrix ι ι ℂ) ⊗ₖ supp RC)
      by rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul], ← Matrix.mul_assoc, h1, h2, htr]
  have e2 : (X * (cfc Real.log RA ⊗ₖ supp RC)).trace =
      (cfc (fun x : ℝ => x * Real.log x) RA).trace := by
    rw [show cfc Real.log RA ⊗ₖ supp RC =
        (cfc Real.log RA ⊗ₖ (1 : Matrix κ κ ℂ)) * ((1 : Matrix ι ι ℂ) ⊗ₖ supp RC)
      by rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul], ← Matrix.mul_assoc,
      Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2', tr_kron_one_right, mul_log _ hA.1]
  have e3 : (X * (supp RA ⊗ₖ cfc Real.log RC)).trace =
      (cfc (fun x : ℝ => x * Real.log x) RC).trace := by
    rw [show supp RA ⊗ₖ cfc Real.log RC =
        (supp RA ⊗ₖ (1 : Matrix κ κ ℂ)) * ((1 : Matrix ι ι ℂ) ⊗ₖ cfc Real.log RC)
      by rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul], ← Matrix.mul_assoc, h1,
      tr_one_kron_right, mul_log _ hC.1]
  rw [e1, e2, e3]
  simp [T, Complex.mul_re]
  ring

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

lemma T_qcq : T (qcq U p rho) = ∑ b, (p b * T (rho b) + p b * Real.log (p b)) := by
  rw [qcq_eq, (emb_oemb _ hU).T_sum (emb_trace _ hU) (fun b => herm_smul (hrho b).1.1)]
  exact Finset.sum_congr rfl fun b _ => T_smul (hp b) (hrho b).1.1 (hrho b).2

lemma T_ab : T (marginalAB (qcq U p rho)) =
    ∑ b, (p b * T (QAlgorithms.traceRight (rho b)) + p b * Real.log (p b)) := by
  rw [ab_eq, (emb_oemb _ hU).T_sum (emb_trace _ hU)
    (fun b => herm_smul (X5UH.tr_psd (hrho b).1).1)]
  exact Finset.sum_congr rfl fun b _ => T_smul (hp b) (X5UH.tr_psd (hrho b).1).1
    ((tr_traceRight _).trans (hrho b).2)

lemma T_bc : T (QAlgorithms.traceLeft (qcq U p rho)) =
    ∑ b, (p b * T (QAlgorithms.traceLeft (rho b)) + p b * Real.log (p b)) := by
  rw [bc_eq, (emb_oemb _ hU).T_sum (emb_trace _ hU)
    (fun b => herm_smul (tl_psd (hrho b).1).1)]
  exact Finset.sum_congr rfl fun b _ => T_smul (hp b) (tl_psd (hrho b).1).1
    ((tr_traceLeft _).trans (hrho b).2)

lemma T_b : T (QAlgorithms.traceRight (QAlgorithms.traceLeft (qcq U p rho))) =
    ∑ b, p b * Real.log (p b) := by
  rw [b_eq U p rho (fun b => (hrho b).2), (emb_oemb _ hU).T_sum (emb_trace _ hU)
    (fun b => herm_smul isHermitian_one)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [T_smul (hp b) isHermitian_one (by simp), T_one]; ring

lemma cmi_qcq : cmi (qcq U p rho) = (∑ b, p b * (T (rho b) - T (QAlgorithms.traceRight (rho b)) -
    T (QAlgorithms.traceLeft (rho b)))) / Real.log 2 := by
  unfold cmi
  rw [vn_eq, vn_eq, vn_eq, vn_eq, T_qcq hU hp hrho, T_ab hU hp hrho, T_bc hU hp hrho,
    T_b hU hp hrho]
  simp only [Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib]
  ring

lemma S_psd (b : B) : ((p b : ℂ) • (QAlgorithms.traceRight (rho b) ⊗ₖ
    QAlgorithms.traceLeft (rho b))).IsHermitian :=
  herm_smul ((X5UH.tr_psd (hrho b).1).kronecker (tl_psd (hrho b).1)).1

lemma rec_herm : (qcqRecovered U p rho).IsHermitian := by
  rw [rec_eq]; exact (emb_oemb _ hU).herm (S_psd hU hp hrho)

lemma qcq_herm : (qcq U p rho).IsHermitian := by
  rw [qcq_eq]; exact (emb_oemb _ hU).herm (fun b => herm_smul (hrho b).1.1)

lemma D_qcq : ((qcq U p rho) * cfc Real.log (qcqRecovered U p rho)).trace.re =
    ∑ b, p b * (Real.log (p b) + T (QAlgorithms.traceRight (rho b)) +
      T (QAlgorithms.traceLeft (rho b))) := by
  rw [rec_eq, (emb_oemb _ hU).cfc_sum (S_psd hU hp hrho) _ Real.log_zero, qcq_eq,
    (emb_oemb _ hU).sum_mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [emb_trace _ hU, block_log (hrho b).1 (hrho b).2 (hp b)]

lemma supp_qcq : qcq U p rho * supp (qcqRecovered U p rho) = qcq U p rho := by
  rw [rec_eq, supp, (emb_oemb _ hU).cfc_sum (S_psd hU hp hrho) _ ind_zero, qcq_eq,
    (emb_oemb _ hU).sum_mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  rcases (hp b).eq_or_lt with h | h
  · rw [← h]; simp
  have hX := (hrho b).1
  rw [← supp, supp_smul h _ ((X5UH.tr_psd hX).kronecker (tl_psd hX)).1,
    supp_kron (X5UH.tr_psd hX) (tl_psd hX), Matrix.smul_mul]
  congr 1
  rw [show supp (QAlgorithms.traceRight (rho b)) ⊗ₖ supp (QAlgorithms.traceLeft (rho b)) =
      (supp (QAlgorithms.traceRight (rho b)) ⊗ₖ (1 : Matrix C C ℂ)) *
        ((1 : Matrix A A ℂ) ⊗ₖ supp (QAlgorithms.traceLeft (rho b)))
      by rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul], ← Matrix.mul_assoc,
    supp_marg_left hX, supp_marg_right hX]

lemma tr_qcq (hsum : ∑ b, p b = 1) : (qcq U p rho).trace = 1 := by
  rw [qcq_eq, Matrix.trace_sum]
  simp only [emb_trace _ hU, Matrix.trace_smul, (hrho _).2, smul_eq_mul, mul_one]
  exact_mod_cast hsum

theorem relEnt_qcq (hsum : ∑ b, p b = 1) :
    normalizedRelativeEntropyBits (qcq U p rho) (qcqRecovered U p rho) =
      ((cmi (qcq U p rho) : ℝ) : EReal) := by
  have htr := tr_qcq hU hp hrho hsum
  have hne : qcq U p rho ≠ 0 := by
    intro h; rw [h, Matrix.trace_zero] at htr; exact zero_ne_one htr
  unfold normalizedRelativeEntropyBits
  rw [if_neg hne]
  unfold QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy
  rw [if_pos (isSupported_of (rec_herm hU hp hrho) (supp_qcq hU hp hrho)), Matrix.trace_sub,
    Complex.sub_re, D_qcq hU hp hrho, cmi_qcq hU hp hrho, htr]
  have hT := T_qcq hU hp hrho
  unfold T at hT
  rw [hT, ← EReal.coe_mul]
  congr 1
  simp only [Complex.one_re, one_mul, div_eq_mul_inv]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold T
  ring

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

lemma emb_psd {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m × B ≃ n) (U : Matrix B B ℂ) (b : B) {Y : Matrix m m ℂ} (hY : Y.PosSemidef) :
    (emb e U b Y).PosSemidef := by
  have h1 : (proj U b).PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  exact (hY.kronecker h1).submatrix e.symm

lemma kraus_sum_smul {I J : Type*} [Fintype I] [Fintype J] {m : ℕ} (K : Fin m → Matrix J I ℂ)
    (c : B → ℂ) (X : B → Matrix I I ℂ) :
    QAlgorithms.krausApply K (∑ b, c b • X b) = ∑ b, c b • QAlgorithms.krausApply K (X b) := by
  unfold QAlgorithms.krausApply
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  rw [Finset.sum_comm]

variable (U : Matrix B B ℂ) (p : B → ℝ) (rho : B → Matrix (A × C) (A × C) ℂ)

lemma blk_eq (a a' : A) :
    (Matrix.of fun i i' => marginalAB (qcq U p rho) (a, i) (a', i')) =
      ∑ b, ((p b : ℂ) * QAlgorithms.traceRight (rho b) a a') •
        (Matrix.of fun i j : B => U i b * conj (U j b)) := by
  ext i j
  simp only [Matrix.of_apply, marginalAB, qcq, QAlgorithms.traceRight, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring

lemma recovery (T : QAlgorithms.Superop B (B × C)) (hT : QAlgorithms.IsChannel T)
    (hbasis : ∀ b, T (fun i j => U i b * conj (U j b)) =
      Matrix.kronecker (fun i j => U i b * conj (U j b)) (QAlgorithms.traceLeft (rho b))) :
    QAlgorithms.idTensorSuperop T (marginalAB (qcq U p rho)) = qcqRecovered U p rho := by
  obtain ⟨m, K, -, hK⟩ := hT
  ext ⟨a, β, c⟩ ⟨a', β', c'⟩
  simp only [QAlgorithms.idTensorSuperop, Matrix.of_apply]
  have hb' : ∀ b, QAlgorithms.krausApply K (Matrix.of fun i j : B => U i b * conj (U j b)) =
      Matrix.kronecker (fun i j => U i b * conj (U j b)) (QAlgorithms.traceLeft (rho b)) :=
    fun b => by rw [← hK]; exact hbasis b
  rw [blk_eq, hK, kraus_sum_smul]
  simp only [hb', Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker_apply, smul_eq_mul,
    qcqRecovered]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.kronecker]; erw [kroneckerMap_apply]
  ring

lemma rec_ab (htr : ∀ b, (rho b).trace = 1) :
    marginalAB (qcqRecovered U p rho) = marginalAB (qcq U p rho) := by
  rw [ab_eq]
  ext x y
  simp only [marginalAB, qcqRecovered, Matrix.sum_apply, emb_apply, Matrix.smul_apply,
    smul_eq_mul, Equiv.refl_symm, Equiv.refl_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h : ∑ c, QAlgorithms.traceLeft (rho b) c c = 1 := by
    rw [← htr b, ← tr_traceLeft]; rfl
  rw [← Finset.mul_sum, h]; ring

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

lemma fid_of_bits {X Y : Matrix (A × (B × C)) (A × (B × C)) ℂ} [Nonempty A] [Nonempty B]
    [Nonempty C] (hX : X.PosSemidef) (hY : Y.PosSemidef) (htr : X.trace = 1) (c : ℝ)
    (h : normalizedRelativeEntropyBits X Y = ((c : ℝ) : EReal)) :
    (2 : ℝ) ^ (-c / 2) ≤ QAlgorithms.rootFidelity X Y := by
  have hre : X.trace.re = 1 := by rw [htr]; simp
  have hm := X5B2.main X Y hX hY (by rw [hre]; norm_num)
  rw [h, hre, div_one] at hm
  set F := QAlgorithms.rootFidelity X Y
  have hF0 : 0 ≤ F := X5B2.psd_re (cfc_nonneg (fun x _ => Real.sqrt_nonneg x) :
    0 ≤ cfc Real.sqrt (cfc Real.sqrt X * Y * cfc Real.sqrt X)).posSemidef
  rcases hF0.eq_or_lt with h0 | hF
  · exfalso
    rw [← h0] at hm
    simp [negLogBits] at hm
  have hF2 : 0 < F ^ 2 := by positivity
  unfold negLogBits at hm
  rw [if_neg (by simpa using hF.ne'), if_neg ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hF2.le, EReal.coe_le_coe_iff] at hm
  have hl : -c / 2 ≤ Real.logb 2 F := by
    rw [show F ^ 2 = F ^ (2 : ℝ) by norm_cast, Real.logb_rpow_eq_mul_logb_of_pos hF] at hm
    linarith
  exact (Real.le_logb_iff_rpow_le (by norm_num) hF).mp hl

theorem classical_conditioning [Nonempty A] [Nonempty B] [Nonempty C]
    (basis : Matrix.unitaryGroup B ℂ) (p : B → ℝ)
    (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, p b = 1)
    (rhoAC : B → Matrix (A × C) (A × C) ℂ) (hrho : ∀ b, QAlgorithms.IsDensityMatrix (rhoAC b))
    (T : QAlgorithms.Superop B (B × C)) (hT : QAlgorithms.IsChannel T)
    (hbasis : ∀ b,
      T (fun i j => (basis : Matrix B B ℂ) i b * conj ((basis : Matrix B B ℂ) j b)) =
        Matrix.kronecker (fun i j => (basis : Matrix B B ℂ) i b * conj ((basis : Matrix B B ℂ) j b))
          (QAlgorithms.traceLeft (rhoAC b))) :
    let rho := qcq (basis : Matrix B B ℂ) p rhoAC
    let sigma := qcqRecovered (basis : Matrix B B ℂ) p rhoAC
    QAlgorithms.idTensorSuperop T (marginalAB rho) = sigma ∧ Markov sigma ∧
      normalizedRelativeEntropyBits rho sigma = ((cmi rho : ℝ) : EReal) ∧
      (2 : ℝ) ^ (-cmi rho / 2) ≤ QAlgorithms.rootFidelity rho sigma := by
  intro rho sigma
  set U := (basis : Matrix B B ℂ)
  have hU : Uᴴ * U = 1 := by
    have := basis.2; rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
  have h1 := recovery U p rhoAC T hT hbasis
  have hrel := relEnt_qcq hU hp hrho hsum
  refine ⟨h1, ⟨T, hT, ?_⟩, hrel, ?_⟩
  · rw [rec_ab U p rhoAC (fun b => (hrho b).2)]; exact h1
  · have hX : rho.PosSemidef := by
      show (qcq U p rhoAC).PosSemidef
      rw [qcq_eq]
      exact Matrix.posSemidef_sum _ fun b _ => emb_psd _ U b ((hrho b).1.smul (by exact_mod_cast hp b))
    have hY : sigma.PosSemidef := by
      show (qcqRecovered U p rhoAC).PosSemidef
      rw [rec_eq]
      exact Matrix.posSemidef_sum _ fun b _ => emb_psd _ U b
        (((X5UH.tr_psd (hrho b).1).kronecker (tl_psd (hrho b).1)).smul (by exact_mod_cast hp b))
    exact fid_of_bits hX hY (tr_qcq hU hp hrho hsum) _ hrel

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

def eL (A B X : Type*) : (A × B) × X ≃ A × (B × X) := Equiv.prodAssoc A B X

/-- the flagged state `Σ p_x ρ_x ⊗ |x⟩⟨x|` with the flag last -/
noncomputable def flag (p : X → ℝ) (rho : X → Matrix (A × B) (A × B) ℂ) :
    Matrix (A × (B × X)) (A × (B × X)) ℂ :=
  ∑ x, emb (eL A B X) (1 : Matrix X X ℂ) x ((p x : ℂ) • rho x)

variable (p : X → ℝ) (rho : X → Matrix (A × B) (A × B) ℂ)

lemma flag_ab : marginalAB (flag p rho) = ∑ x, (p x : ℂ) • rho x := by
  ext y z
  simp only [marginalAB, flag, Matrix.sum_apply, emb_apply, Matrix.smul_apply, smul_eq_mul, eL,
    Equiv.prodAssoc_symm_apply, Matrix.one_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x (fun b _ hb => by simp [hb]) (by simp)]
  simp

lemma flag_bx : QAlgorithms.traceLeft (flag p rho) =
    ∑ x, emb (Equiv.refl (B × X)) (1 : Matrix X X ℂ) x ((p x : ℂ) • QAlgorithms.traceLeft (rho x)) := by
  ext ⟨b, y⟩ ⟨b', z⟩
  simp only [QAlgorithms.traceLeft, flag, Matrix.sum_apply, emb_apply, Matrix.smul_apply,
    smul_eq_mul, eL, Equiv.prodAssoc_symm_apply, Matrix.of_apply, Equiv.refl_symm,
    Equiv.refl_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

lemma flag_b : QAlgorithms.traceRight (QAlgorithms.traceLeft (flag p rho)) =
    ∑ x, (p x : ℂ) • QAlgorithms.traceLeft (rho x) := by
  rw [flag_bx]
  ext y z
  simp only [QAlgorithms.traceRight, Matrix.sum_apply, emb_apply, Matrix.smul_apply, smul_eq_mul,
    Equiv.refl_symm, Equiv.refl_apply, Matrix.one_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x (fun b _ hb => by simp [hb]) (by simp)]
  simp

lemma tl_sum (c : X → ℂ) (Y : X → Matrix (A × B) (A × B) ℂ) :
    QAlgorithms.traceLeft (∑ x, c x • Y x) = ∑ x, c x • QAlgorithms.traceLeft (Y x) := by
  ext i j
  simp only [QAlgorithms.traceLeft, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

variable {p rho}

lemma flag_density (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (hrho : ∀ x, QAlgorithms.IsDensityMatrix (rho x)) :
    QAlgorithms.IsDensityMatrix (flag p rho) := by
  have hU : (1 : Matrix X X ℂ)ᴴ * 1 = 1 := by simp
  refine ⟨Matrix.posSemidef_sum _ fun x _ => emb_psd _ _ x ((hrho x).1.smul (by exact_mod_cast hp x)), ?_⟩
  rw [flag, Matrix.trace_sum]
  simp only [emb_trace _ hU, Matrix.trace_smul, (hrho _).2, smul_eq_mul, mul_one]
  exact_mod_cast hsum

/-- Concavity of the conditional entropy `H(AB) - H(B)`, from strong subadditivity. -/
theorem condEnt_concave [Nonempty A] [Nonempty B] [Nonempty X]
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (hrho : ∀ x, QAlgorithms.IsDensityMatrix (rho x)) :
    ∑ x, p x * (QAlgorithms.vnEntropy (rho x) -
      QAlgorithms.vnEntropy (QAlgorithms.traceLeft (rho x))) ≤
    QAlgorithms.vnEntropy (∑ x, (p x : ℂ) • rho x) -
      QAlgorithms.vnEntropy (QAlgorithms.traceLeft (∑ x, (p x : ℂ) • rho x)) := by
  have hU : (1 : Matrix X X ℂ)ᴴ * 1 = 1 := by simp
  have h := QAlgorithms.Papers.Independent.Claimed50.P12.backgroundSSA (flag p rho)
    (flag_density hp hsum hrho)
  unfold cmi at h
  rw [flag_ab, flag_b, flag_bx] at h
  rw [tl_sum]
  have e1 : QAlgorithms.vnEntropy (flag p rho) =
      -(∑ x, (p x * T (rho x) + p x * Real.log (p x))) / Real.log 2 := by
    rw [vn_eq, flag, (emb_oemb _ hU).T_sum (emb_trace _ hU) (fun x => herm_smul (hrho x).1.1)]
    congr 2
    exact Finset.sum_congr rfl fun x _ => T_smul (hp x) (hrho x).1.1 (hrho x).2
  have e2 : QAlgorithms.vnEntropy (∑ x, emb (Equiv.refl (B × X)) (1 : Matrix X X ℂ) x
      ((p x : ℂ) • QAlgorithms.traceLeft (rho x))) =
      -(∑ x, (p x * T (QAlgorithms.traceLeft (rho x)) + p x * Real.log (p x))) / Real.log 2 := by
    rw [vn_eq, (emb_oemb _ hU).T_sum (emb_trace _ hU)
      (fun x => herm_smul (tl_psd (hrho x).1).1)]
    congr 2
    exact Finset.sum_congr rfl fun x _ => T_smul (hp x) (tl_psd (hrho x).1).1
      ((tr_traceLeft _).trans (hrho x).2)
  rw [e1, e2] at h
  simp only [vn_eq]
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [← sub_nonneg]
  have : ∑ x, p x * (-T (rho x) / Real.log 2 - -T (QAlgorithms.traceLeft (rho x)) / Real.log 2) =
      (∑ x, (p x * T (QAlgorithms.traceLeft (rho x)) + p x * Real.log (p x)) -
        ∑ x, (p x * T (rho x) + p x * Real.log (p x))) / Real.log 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    field_simp; ring
  rw [this]
  have h2 : 0 ≤ -T (∑ x, (p x : ℂ) • rho x) / Real.log 2 +
      -(∑ x, (p x * T (QAlgorithms.traceLeft (rho x)) + p x * Real.log (p x))) / Real.log 2 -
      -T (∑ x, (p x : ℂ) • QAlgorithms.traceLeft (rho x)) / Real.log 2 -
      -(∑ x, (p x * T (rho x) + p x * Real.log (p x))) / Real.log 2 := by
    simpa only [vn_eq] using h
  convert h2 using 1
  ring

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

/-- `A × (X × X) ≃ X × (A × X)` -/
def eD (A X : Type*) : A × (X × X) ≃ X × (A × X) where
  toFun y := (y.2.1, (y.1, y.2.2))
  invFun y := (y.2.1, (y.1, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Σ_x p_x |x⟩⟨x| ⊗ ρ_x ⊗ |x⟩⟨x|` -/
noncomputable def dflag (p : X → ℝ) (rho : X → Matrix A A ℂ) : Matrix (X × (A × X)) (X × (A × X)) ℂ :=
  ∑ b : X × X, emb (eD A X) (1 : Matrix (X × X) (X × X) ℂ) b
    (if b.1 = b.2 then (p b.1 : ℂ) • rho b.1 else 0)

variable (p : X → ℝ) (rho : X → Matrix A A ℂ)

lemma dflag_apply (x : X) (a : A) (x2 : X) (x' : X) (a' : A) (x2' : X) :
    dflag p rho (x, (a, x2)) (x', (a', x2')) = if x = x2 ∧ x' = x2' ∧ x = x' then
      (p x : ℂ) * rho x a a' else 0 := by
  simp only [dflag, Matrix.sum_apply, emb_apply, eD, Equiv.coe_fn_symm_mk, Matrix.one_apply]
  rw [Finset.sum_eq_single (x, x2)]
  · by_cases h1 : x = x2
    · subst h1
      by_cases h3 : x = x'
      · subst h3
        by_cases h2 : x = x2'
        · simp [h2]
        · have h2' : x2' ≠ x := fun h => h2 h.symm
          simp [h2, h2']
      · simp [h3, Ne.symm h3]
    · simp [h1]
  · intro c _ hc; simp [Ne.symm hc]
  · simp

lemma dflag_ab : marginalAB (dflag p rho) =
    ∑ x, emb (Equiv.prodComm A X) (1 : Matrix X X ℂ) x ((p x : ℂ) • rho x) := by
  ext ⟨x, a⟩ ⟨x', a'⟩
  simp only [marginalAB, dflag_apply, Matrix.sum_apply, emb_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.swap_prod_mk, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : x = x'
  · subst h; simp only [ite_and]; simp
    rw [Finset.sum_eq_single x (fun c _ hc => by simp [Ne.symm hc]) (by simp)]; simp
  · simp [h, ite_and, Ne.symm h]
    refine (Finset.sum_eq_zero fun c _ => ?_).symm
    by_cases hc : x = c
    · subst hc
      have h' : ¬ x' = x := fun e => h e.symm
      simp only [h', if_false, map_zero, mul_zero]
    · simp [hc]

lemma dflag_ax : QAlgorithms.traceLeft (dflag p rho) =
    ∑ x, emb (Equiv.refl (A × X)) (1 : Matrix X X ℂ) x ((p x : ℂ) • rho x) := by
  ext ⟨a, x⟩ ⟨a', x'⟩
  simp only [QAlgorithms.traceLeft, Matrix.of_apply, dflag_apply, Matrix.sum_apply, emb_apply,
    Equiv.refl_symm, Equiv.refl_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : x = x'
  · subst h; simp only [ite_and]; simp
    rw [Finset.sum_eq_single x (fun c _ hc => by simp [Ne.symm hc]) (by simp)]; simp
  · simp [h, ite_and, Ne.symm h]
    refine (Finset.sum_eq_zero fun c _ => ?_).symm
    by_cases hc : x = c
    · subst hc
      have h' : ¬ x' = x := fun e => h e.symm
      simp only [h', if_false, map_zero, mul_zero]
    · simp [hc]

lemma dflag_a : QAlgorithms.traceRight (QAlgorithms.traceLeft (dflag p rho)) =
    ∑ x, (p x : ℂ) • rho x := by
  rw [dflag_ax]
  ext a a'
  simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.sum_apply, emb_apply,
    Equiv.refl_symm, Equiv.refl_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x (fun c _ hc => by simp [hc]) (by simp)]
  simp

lemma T_zero : T (0 : Matrix A A ℂ) = 0 := by simp [T]

variable {p rho}

lemma dflag_T (hp : ∀ x, 0 ≤ p x) (hrho : ∀ x, QAlgorithms.IsDensityMatrix (rho x)) :
    T (dflag p rho) = ∑ x, (p x * T (rho x) + p x * Real.log (p x)) := by
  have hU : (1 : Matrix (X × X) (X × X) ℂ)ᴴ * 1 = 1 := by simp
  have hY : ∀ b : X × X, (if b.1 = b.2 then (p b.1 : ℂ) • rho b.1 else 0).IsHermitian := by
    intro b; split_ifs
    · exact herm_smul (hrho _).1.1
    · exact isHermitian_zero
  rw [dflag, (emb_oemb _ hU).T_sum (emb_trace _ hU) hY, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x (fun c _ hc => by rw [if_neg (Ne.symm hc), T_zero]) (by simp),
    if_pos rfl, T_smul (hp x) (hrho x).1.1 (hrho x).2]

lemma dflag_density (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (hrho : ∀ x, QAlgorithms.IsDensityMatrix (rho x)) :
    QAlgorithms.IsDensityMatrix (dflag p rho) := by
  have hU : (1 : Matrix (X × X) (X × X) ℂ)ᴴ * 1 = 1 := by simp
  refine ⟨Matrix.posSemidef_sum _ fun b _ => emb_psd _ _ b ?_, ?_⟩
  · split_ifs
    · exact (hrho _).1.smul (by exact_mod_cast hp _)
    · exact Matrix.PosSemidef.zero
  rw [dflag, Matrix.trace_sum, Fintype.sum_prod_type]
  simp only [emb_trace _ hU]
  rw [show (1 : ℂ) = ((∑ x, p x : ℝ) : ℂ) by rw [hsum]; simp]; push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x (fun c _ hc => by rw [if_neg (Ne.symm hc), Matrix.trace_zero])
    (by simp), if_pos rfl, Matrix.trace_smul, (hrho x).2, smul_eq_mul, mul_one]

lemma vn_embsum {n : Type*} [Fintype n] [DecidableEq n] (e' : A × X ≃ n)
    (hp : ∀ x, 0 ≤ p x) (hrho : ∀ x, QAlgorithms.IsDensityMatrix (rho x)) :
    QAlgorithms.vnEntropy (∑ x, emb e' (1 : Matrix X X ℂ) x ((p x : ℂ) • rho x)) =
      -(∑ x, (p x * T (rho x) + p x * Real.log (p x))) / Real.log 2 := by
  have hU : (1 : Matrix X X ℂ)ᴴ * 1 = 1 := by simp
  rw [vn_eq, (emb_oemb _ hU).T_sum (emb_trace _ hU) (fun x => herm_smul (hrho x).1.1)]
  congr 2
  exact Finset.sum_congr rfl fun x _ => T_smul (hp x) (hrho x).1.1 (hrho x).2

/-- `H(Σ p_x ρ_x) ≤ Σ p_x H(ρ_x) + H(p)`, from strong subadditivity. -/
theorem mix_entropy [Nonempty A] [Nonempty X] (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (hrho : ∀ x, QAlgorithms.IsDensityMatrix (rho x)) :
    QAlgorithms.vnEntropy (∑ x, (p x : ℂ) • rho x) ≤
      ∑ x, p x * QAlgorithms.vnEntropy (rho x) - ∑ x, p x * Real.logb 2 (p x) := by
  have hU : (1 : Matrix X X ℂ)ᴴ * 1 = 1 := by simp
  have h := QAlgorithms.Papers.Independent.Claimed50.P12.backgroundSSA (dflag p rho)
    (dflag_density hp hsum hrho)
  unfold cmi at h
  rw [dflag_ab, dflag_a, dflag_ax] at h
  rw [vn_embsum _ hp hrho, vn_embsum _ hp hrho, vn_eq (dflag p rho), dflag_T hp hrho] at h
  simp only [vn_eq, Real.logb]
  have : ∑ x, p x * (-T (rho x) / Real.log 2) - ∑ x, p x * (Real.log (p x) / Real.log 2) =
      -(∑ x, (p x * T (rho x) + p x * Real.log (p x))) / Real.log 2 := by
    rw [← Finset.sum_sub_distrib, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [this]
  simp only [vn_eq] at h
  linarith

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

lemma T_ge {X : Matrix ι ι ℂ} (hX : QAlgorithms.IsDensityMatrix X) :
    -Real.log (Fintype.card ι) ≤ T X := by
  have hH := hX.1.1
  have hT : T X = ∑ i, hH.eigenvalues i * Real.log (hH.eigenvalues i) := by
    unfold T; rw [tr_cfc hH, Complex.re_sum]; simp
  have hs : ∑ i, hH.eigenvalues i = 1 := by
    have := hX.2
    rw [hH.trace_eq_sum_eigenvalues] at this
    have := congrArg Complex.re this
    simpa using this
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := hX.1.eigenvalues_nonneg
  set d : ℝ := (Fintype.card ι : ℝ)
  have hd : 0 < d := by
    have : 0 < Fintype.card ι := by
      by_contra h0
      have he : IsEmpty ι := Fintype.card_eq_zero_iff.1 (by omega)
      rw [Finset.univ_eq_empty] at hs; simp at hs
    simp only [d]; exact_mod_cast this
  have key : ∀ i, hH.eigenvalues i - 1 / d ≤
      hH.eigenvalues i * Real.log (hH.eigenvalues i) + hH.eigenvalues i * Real.log d := by
    intro i
    rcases (hnn i).lt_or_eq with h | h
    · have := Real.one_sub_inv_le_log_of_pos (mul_pos h hd)
      rw [Real.log_mul h.ne' hd.ne'] at this
      have e : hH.eigenvalues i * (1 - (hH.eigenvalues i * d)⁻¹) = hH.eigenvalues i - 1 / d := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_left this h.le]
    · rw [← h]; simp; positivity
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
  rw [Finset.sum_sub_distrib, hs, Finset.sum_add_distrib, ← Finset.sum_mul, hs, ← hT] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have : (Fintype.card ι : ℝ) * (1 / d) = 1 := by
    rw [mul_one_div]; exact div_self hd.ne'
  linarith

lemma vn_le {X : Matrix ι ι ℂ} (hX : QAlgorithms.IsDensityMatrix X) :
    QAlgorithms.vnEntropy X ≤ Real.logb 2 (Fintype.card ι) := by
  rw [vn_eq, Real.logb, neg_div]
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [neg_le, ← neg_div]
  exact div_le_div_of_nonneg_right (T_ge hX) hl.le

/-! transpose invariance -/

lemma tr_aeval_transpose (X : Matrix ι ι ℂ) (p : ℝ[X]) :
    (aeval Xᵀ p).trace = (aeval X p).trace := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, Matrix.trace_smul, ← Matrix.transpose_pow, Matrix.trace_transpose]

lemma tr_cfc_transpose {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    (cfc f Xᵀ).trace = (cfc f X).trace := by
  have hA : IsSelfAdjoint Xᵀ := hX.transpose.isSelfAdjoint
  have hB : IsSelfAdjoint X := hX.isSelfAdjoint
  have fA : (spectrum ℝ Xᵀ).Finite := Xᵀ.finite_real_spectrum
  have fB : (spectrum ℝ X).Finite := X.finite_real_spectrum
  set s : Finset ℝ := fA.toFinset ∪ fB.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have h1 : cfc f Xᵀ = cfc (fun x => p.eval x) Xᵀ :=
    cfc_congr fun x hx => (hp x (by simp [s, fA.mem_toFinset.2 hx])).symm
  have h2 : cfc f X = cfc (fun x => p.eval x) X :=
    cfc_congr fun x hx => (hp x (by simp [s, fB.mem_toFinset.2 hx])).symm
  rw [h1, h2, cfc_polynomial p _ hA, cfc_polynomial p X hB]
  exact tr_aeval_transpose X p

lemma T_transpose {X : Matrix ι ι ℂ} (hX : X.IsHermitian) : T Xᵀ = T X := by
  unfold T; rw [tr_cfc_transpose hX]

lemma T_swap {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) : T (Mᴴ * M) = T (M * Mᴴ) := by
  unfold T; rw [X5UH.tr_cfc_swap M _ (by simp)]

end X5AF
end X5mod_AF_Bounds

section X5mod_AF_Cond
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5AF
open X5QC
set_option linter.unusedSectionVars false

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- conditional entropy `H(AB) - H(B)` in bits, `B` the second factor -/
noncomputable def Hc (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  QAlgorithms.vnEntropy rho - QAlgorithms.vnEntropy (QAlgorithms.traceLeft rho)

lemma trR_dens {rho : Matrix (A × B) (A × B) ℂ} (h : QAlgorithms.IsDensityMatrix rho) :
    QAlgorithms.IsDensityMatrix (QAlgorithms.traceRight rho) :=
  ⟨X5UH.tr_psd h.1, (tr_traceRight _).trans h.2⟩

lemma trL_dens {rho : Matrix (A × B) (A × B) ℂ} (h : QAlgorithms.IsDensityMatrix rho) :
    QAlgorithms.IsDensityMatrix (QAlgorithms.traceLeft rho) :=
  ⟨tl_psd h.1, (tr_traceLeft _).trans h.2⟩

lemma Hc_le {rho : Matrix (A × B) (A × B) ℂ} (h : QAlgorithms.IsDensityMatrix rho) :
    Hc rho ≤ Real.logb 2 (Fintype.card A) := by
  have h1 := QAlgorithms.Arunachalam.vnEntropy_subadditive rho h
  have h2 := vn_le (trR_dens h)
  unfold Hc; linarith

/-- the matrix of the canonical purification, regrouped as `B | A R` -/
noncomputable def Mp (rho : Matrix (A × B) (A × B) ℂ) : Matrix B (A × (A × B)) ℂ :=
  fun b ar => cfc Real.sqrt rho (ar.1, b) ar.2

lemma Mp_mul {rho : Matrix (A × B) (A × B) ℂ} (h : rho.PosSemidef) :
    Mp rho * (Mp rho)ᴴ = QAlgorithms.traceLeft rho := by
  conv_rhs => rw [← X5B2.sqrt_sq h]
  conv_rhs => enter [1, 2]; rw [← X5B2.sqrt_herm rho]
  ext b b'
  simp [Mp, Matrix.mul_apply, QAlgorithms.traceLeft, Fintype.sum_prod_type]

lemma tau_trR {rho : Matrix (A × B) (A × B) ℂ} (h : rho.PosSemidef) :
    QAlgorithms.traceRight ((Mp rho)ᴴ * Mp rho)ᵀ = QAlgorithms.traceRight rho := by
  conv_rhs => rw [← X5B2.sqrt_sq h]
  conv_rhs => enter [1, 2]; rw [← X5B2.sqrt_herm rho]
  ext a a'
  simp only [QAlgorithms.traceRight, Matrix.transpose_apply, Matrix.mul_apply, Mp,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.of_apply]
  refine (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun y _ => ?_
  simp [mul_comm]

lemma tau_trL {rho : Matrix (A × B) (A × B) ℂ} (h : rho.PosSemidef) :
    QAlgorithms.traceLeft ((Mp rho)ᴴ * Mp rho)ᵀ = rhoᵀ := by
  conv_rhs => rw [← X5B2.sqrt_sq h]
  conv_rhs => enter [1, 1]; rw [← X5B2.sqrt_herm rho]
  ext r r'
  simp only [QAlgorithms.traceLeft, Matrix.transpose_apply, Matrix.mul_apply, Mp,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.of_apply]

lemma Hc_ge {rho : Matrix (A × B) (A × B) ℂ} (h : QAlgorithms.IsDensityMatrix rho) :
    -Real.logb 2 (Fintype.card A) ≤ Hc rho := by
  set τ := ((Mp rho)ᴴ * Mp rho)ᵀ
  have hτ : QAlgorithms.IsDensityMatrix τ := by
    refine ⟨(Matrix.posSemidef_conjTranspose_mul_self _).transpose, ?_⟩
    rw [Matrix.trace_transpose, Matrix.trace_mul_comm, Mp_mul h.1, tr_traceLeft, h.2]
  have h1 := QAlgorithms.Arunachalam.vnEntropy_subadditive τ hτ
  rw [tau_trR h.1, tau_trL h.1] at h1
  have e1 : QAlgorithms.vnEntropy τ = QAlgorithms.vnEntropy (QAlgorithms.traceLeft rho) := by
    rw [vn_eq, vn_eq, T_transpose (Matrix.isHermitian_conjTranspose_mul_self _), T_swap, Mp_mul h.1]
  have e2 : QAlgorithms.vnEntropy rhoᵀ = QAlgorithms.vnEntropy rho := by
    rw [vn_eq, vn_eq, T_transpose h.1.1]
  have h2 := vn_le (trR_dens h)
  unfold Hc; linarith

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

noncomputable def lift (Y : Matrix B B ℂ) : Matrix (B × Unit) (B × Unit) ℂ :=
  emb (Equiv.refl (B × Unit)) (1 : Matrix Unit Unit ℂ) () Y

lemma vn_lift {Y : Matrix B B ℂ} (hY : QAlgorithms.IsDensityMatrix Y) :
    QAlgorithms.vnEntropy (lift Y) = QAlgorithms.vnEntropy Y := by
  have h := vn_embsum (X := Unit) (p := fun _ => (1 : ℝ)) (rho := fun _ => Y) (Equiv.refl (B × Unit))
    (fun _ => zero_le_one) (fun _ => hY)
  simp only [Finset.univ_unique, Finset.sum_singleton, Complex.ofReal_one, one_smul, one_mul,
    Real.log_one, add_zero] at h
  rw [lift, h, vn_eq]

lemma vn_unit {M : Matrix Unit Unit ℂ} (hM : QAlgorithms.IsDensityMatrix M) :
    QAlgorithms.vnEntropy M = 0 := by
  have : M = 1 := by
    ext i j
    have h := hM.2
    simp only [Matrix.trace, Finset.univ_unique, Finset.sum_singleton, Matrix.diag_apply] at h
    rw [Subsingleton.elim i default, Subsingleton.elim j default, h]; simp
  rw [this, vn_eq, T_one]; simp

lemma lift_dens {Y : Matrix B B ℂ} (hY : QAlgorithms.IsDensityMatrix Y) :
    QAlgorithms.IsDensityMatrix (lift Y) := by
  have hU : (1 : Matrix Unit Unit ℂ)ᴴ * 1 = 1 := by simp
  exact ⟨emb_psd _ _ _ hY.1, (emb_trace _ hU _ _).trans hY.2⟩

theorem vn_concave [Nonempty B] [Nonempty X] (p : X → ℝ) (Y : X → Matrix B B ℂ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) (hY : ∀ x, QAlgorithms.IsDensityMatrix (Y x)) :
    ∑ x, p x * QAlgorithms.vnEntropy (Y x) ≤ QAlgorithms.vnEntropy (∑ x, (p x : ℂ) • Y x) := by
  have hm : QAlgorithms.IsDensityMatrix (∑ x, (p x : ℂ) • Y x) := by
    refine ⟨Matrix.posSemidef_sum _ fun x _ => (hY x).1.smul (by exact_mod_cast hp x), ?_⟩
    rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, (hY _).2, smul_eq_mul, mul_one]
    exact_mod_cast hsum
  have h := condEnt_concave (B := Unit) (p := p) (rho := fun x => lift (Y x)) hp hsum (fun x => lift_dens (hY x))
  have hl : ∑ x, (p x : ℂ) • lift (Y x) = lift (∑ x, (p x : ℂ) • Y x) := by
    simp only [lift, map_sum, map_smul]
  rw [hl, vn_lift hm, vn_unit (trL_dens (lift_dens hm))] at h
  simp only [vn_lift (hY _), vn_unit (trL_dens (lift_dens (hY _))), sub_zero] at h
  exact h

theorem Hc_mix [Nonempty A] [Nonempty B] [Nonempty X] (p : X → ℝ)
    (rho : X → Matrix (A × B) (A × B) ℂ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) (hrho : ∀ x, QAlgorithms.IsDensityMatrix (rho x)) :
    Hc (∑ x, (p x : ℂ) • rho x) ≤ ∑ x, p x * Hc (rho x) - ∑ x, p x * Real.logb 2 (p x) := by
  have h1 := mix_entropy (p := p) (rho := rho) hp hsum hrho
  have h2 := vn_concave p (fun x => QAlgorithms.traceLeft (rho x)) hp hsum
    (fun x => trL_dens (hrho x))
  unfold Hc
  rw [tl_sum]
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

theorem Hc_concave [Nonempty A] [Nonempty B] [Nonempty X] (p : X → ℝ)
    (rho : X → Matrix (A × B) (A × B) ℂ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) (hrho : ∀ x, QAlgorithms.IsDensityMatrix (rho x)) :
    ∑ x, p x * Hc (rho x) ≤ Hc (∑ x, (p x : ℂ) • rho x) :=
  condEnt_concave (p := p) (rho := rho) hp hsum hrho

end X5AF
end X5mod_AF_Mix2

section X5mod_QK_Vec
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QK
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- `vec M = (M ⊗ 1)|Φ⟩`. -/
noncomputable def vecE (M : Matrix I I ℂ) : EuclideanSpace ℂ (I × I) :=
  WithLp.toLp 2 (fun p => M p.1 p.2)

lemma trR_vec (M : Matrix I I ℂ) :
    QAlgorithms.traceRight (QAlgorithms.pureDensity (vecE M)) = M * Mᴴ := by
  ext i j
  simp [QAlgorithms.traceRight, QAlgorithms.pureDensity, vecE, Matrix.mul_apply]

lemma trL_vec (M : Matrix I I ℂ) :
    QAlgorithms.traceLeft (QAlgorithms.pureDensity (vecE M)) = (Mᴴ * M)ᵀ := by
  ext i j
  simp [QAlgorithms.traceLeft, QAlgorithms.pureDensity, vecE, Matrix.mul_apply, mul_comm]

lemma inner_vec (M N : Matrix I I ℂ) : inner ℂ (vecE M) (vecE N) = (Mᴴ * N).trace := by
  simp only [vecE, PiLp.inner_apply, RCLike.inner_apply, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, conjTranspose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

lemma norm_vec_sq (M : Matrix I I ℂ) : ‖vecE M‖ ^ 2 = (Mᴴ * M).trace.re := by
  rw [← inner_vec, inner_self_eq_norm_sq_to_K]
  norm_cast

end X5QK
end X5mod_QK_Vec

section X5mod_QK_Ops
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QK
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma sq_psd {X : Matrix I I ℂ} (h : X.PosSemidef) : (cfc Real.sqrt X).PosSemidef :=
  (cfc_nonneg (fun x _ => Real.sqrt_nonneg x) : 0 ≤ cfc Real.sqrt X).posSemidef

lemma conj_psd {X : Matrix I I ℂ} (h : X.PosSemidef) (C : Matrix I I ℂ) (hC : Cᴴ = C) :
    (C * X * C).PosSemidef := by
  have := h.mul_mul_conjTranspose_same C; rwa [hC] at this

/-- `Tr (P Q) ≥ 0` for PSD `P, Q`. -/
lemma tr_mul_psd {P Q : Matrix I I ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    (P * Q).trace = (((P * Q).trace.re : ℝ) : ℂ) ∧ 0 ≤ (P * Q).trace.re := by
  set a := cfc Real.sqrt P
  have e : (P * Q).trace = (a * Q * a).trace := by
    rw [← X5B2.sqrt_sq hP, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h := conj_psd hQ a (X5B2.sqrt_herm P)
  rw [e]
  exact ⟨X5UH.psd_tr h, X5B2.psd_re h⟩

lemma tr_mono {P A B : Matrix I I ℂ} (hP : P.PosSemidef) (hAB : (B - A).PosSemidef) :
    (P * A).trace.re ≤ (P * B).trace.re := by
  have := (tr_mul_psd hP hAB).2
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at this
  linarith

/-- `|Tr (Z Δ)| ≤ Tr Δ` for a contraction `Z Z† ≤ 1` and PSD `Δ`. -/
lemma abs_tr_contr {Z D : Matrix I I ℂ} (hZ : (1 - Z * Zᴴ).PosSemidef) (hD : D.PosSemidef) :
    ‖(Z * D).trace‖ ≤ D.trace.re := by
  set a := cfc Real.sqrt D
  have ha : aᴴ = a := X5B2.sqrt_herm D
  have haa : a * a = D := X5B2.sqrt_sq hD
  have e : (Z * D).trace = inner ℂ (vecE (Zᴴ * a)) (vecE a) := by
    rw [inner_vec, conjTranspose_mul, conjTranspose_conjTranspose, ha, ← haa,
      Matrix.trace_mul_comm, Matrix.mul_assoc]
    exact Matrix.trace_mul_comm a (a * Z)
  have n1 : ‖vecE (Zᴴ * a)‖ ^ 2 ≤ D.trace.re := by
    rw [norm_vec_sq, conjTranspose_mul, conjTranspose_conjTranspose, ha]
    have := (tr_mul_psd (conj_psd hZ a ha) Matrix.PosSemidef.one).2
    rw [Matrix.mul_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, haa, Matrix.trace_sub,
      Complex.sub_re] at this
    rw [show a * Z * (Zᴴ * a) = a * (Z * Zᴴ) * a by simp only [Matrix.mul_assoc]]
    linarith
  have n2 : ‖vecE a‖ ^ 2 = D.trace.re := by rw [norm_vec_sq, ha, haa]
  rw [e]
  refine (norm_inner_le_norm _ _).trans ?_
  have h0 : 0 ≤ D.trace.re := X5B2.psd_re hD
  have hb : ‖vecE (Zᴴ * a)‖ ≤ Real.sqrt D.trace.re :=
    Real.le_sqrt_of_sq_le n1
  have hc : ‖vecE a‖ = Real.sqrt D.trace.re := by
    rw [← n2, Real.sqrt_sq (norm_nonneg _)]
  rw [hc]
  calc ‖vecE (Zᴴ * a)‖ * Real.sqrt D.trace.re ≤ Real.sqrt D.trace.re * Real.sqrt D.trace.re :=
        mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _)
    _ = D.trace.re := Real.mul_self_sqrt h0

/-- generalized inverse square root -/
noncomputable def isq (X : Matrix I I ℂ) : Matrix I I ℂ := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) X

lemma isq_herm (X : Matrix I I ℂ) : (isq X)ᴴ = isq X := (cfc_predicate _ X : IsSelfAdjoint _)

lemma isq_mul {X : Matrix I I ℂ} (hX : X.PosSemidef) : isq X * X = cfc Real.sqrt X := by
  unfold isq
  nth_rewrite 2 [← cfc_id' ℝ X hX.1.isSelfAdjoint]
  rw [← cfc_mul _ _ _ (X5B2.fin _ _) (X5B2.fin _ _)]
  refine cfc_congr fun x hx => ?_
  have h0 : 0 ≤ x := spectrum_nonneg_of_nonneg hX.nonneg hx
  rcases h0.eq_or_lt with h | h
  · subst h; simp
  rw [inv_mul_eq_div, Real.div_sqrt]

lemma isq_conj {X : Matrix I I ℂ} (hX : X.PosSemidef) : isq X * X * isq X = X5QC.supp X := by
  rw [isq_mul hX]
  unfold isq X5QC.supp
  rw [← cfc_mul _ _ _ (X5B2.fin _ _) (X5B2.fin _ _)]
  refine cfc_congr fun x hx => ?_
  have h0 : 0 ≤ x := spectrum_nonneg_of_nonneg hX.nonneg hx
  rcases h0.eq_or_lt with h | h
  · subst h; simp [X5QC.ind]
  rw [mul_inv_cancel₀ (Real.sqrt_pos.2 h).ne', X5QC.ind, if_neg h.ne']

lemma one_sub_supp {X : Matrix I I ℂ} (hX : X.IsHermitian) : (1 - X5QC.supp X).PosSemidef := by
  have : 1 - X5QC.supp X = cfc (fun x => 1 - X5QC.ind x) X := by
    rw [cfc_sub _ _ _ (X5B2.fin _ _) (X5B2.fin _ _), cfc_const_one ℝ X hX.isSelfAdjoint]; rfl
  rw [this]
  refine (cfc_nonneg fun x _ => ?_ : 0 ≤ cfc (fun x => 1 - X5QC.ind x) X).posSemidef
  unfold X5QC.ind; split_ifs <;> norm_num

end X5QK
end X5mod_QK_Ops

section X5mod_QK_Pure
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QK
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- positive / negative parts -/
noncomputable def Hp (H : Matrix I I ℂ) : Matrix I I ℂ := cfc (fun x : ℝ => max x 0) H
noncomputable def Hm (H : Matrix I I ℂ) : Matrix I I ℂ := cfc (fun x : ℝ => max (-x) 0) H

lemma Hp_psd (H : Matrix I I ℂ) : (Hp H).PosSemidef :=
  (cfc_nonneg (fun x _ => le_max_right x 0) : 0 ≤ cfc (fun x : ℝ => max x 0) H).posSemidef

lemma Hm_psd (H : Matrix I I ℂ) : (Hm H).PosSemidef :=
  (cfc_nonneg (fun x _ => le_max_right (-x) 0) : 0 ≤ cfc (fun x : ℝ => max (-x) 0) H).posSemidef

lemma H_eq {H : Matrix I I ℂ} (hH : H.IsHermitian) : H = Hp H - Hm H := by
  unfold Hp Hm
  rw [← cfc_sub _ _ _ (X5B2.fin _ _) (X5B2.fin _ _)]
  conv_lhs => rw [← cfc_id' ℝ H hH.isSelfAdjoint]
  refine cfc_congr fun x _ => ?_
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

lemma traceNorm_eq {H : Matrix I I ℂ} (hH : H.IsHermitian) :
    QAlgorithms.traceNorm H = (Hp H).trace.re + (Hm H).trace.re := by
  unfold QAlgorithms.traceNorm
  rw [hH.eq]
  have e : H * H = cfc (fun x : ℝ => x * x) H := by
    rw [cfc_mul _ _ _ (X5B2.fin _ _) (X5B2.fin _ _), cfc_id' ℝ H hH.isSelfAdjoint]
  rw [e, ← cfc_comp Real.sqrt (fun x : ℝ => x * x) H hH.isSelfAdjoint ((H.finite_real_spectrum.image _).continuousOn _) (X5B2.fin _ _),
    ← Complex.add_re, ← Matrix.trace_add, Hp, Hm, ← cfc_add _ _ _ (X5B2.fin _ _) (X5B2.fin _ _)]
  congr 2
  refine cfc_congr fun x _ => ?_
  simp only [Function.comp, Real.sqrt_mul_self_eq_abs]
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring

/-- the pure density of a vector as `vecMulVec` -/
lemma pd_eq (v : EuclideanSpace ℂ I) :
    QAlgorithms.pureDensity v = vecMulVec v.ofLp (star v.ofLp) := by
  ext i j; simp [QAlgorithms.pureDensity, vecMulVec_apply]

lemma inner_eq (v w : EuclideanSpace ℂ I) : inner ℂ v w = star v.ofLp ⬝ᵥ w.ofLp := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

lemma pd_psd (v : EuclideanSpace ℂ I) : (QAlgorithms.pureDensity v).PosSemidef := by
  rw [pd_eq]; exact Matrix.posSemidef_vecMulVec_self_star _

lemma pd_trace (v : EuclideanSpace ℂ I) : (QAlgorithms.pureDensity v).trace = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [pd_eq, X5UH.norm_sq_eq, Matrix.trace_vecMulVec]
  simp [dotProduct, mul_comm]

lemma pd_idem {v : EuclideanSpace ℂ I} (hv : ‖v‖ = 1) :
    QAlgorithms.pureDensity v * QAlgorithms.pureDensity v = QAlgorithms.pureDensity v := by
  have h : star v.ofLp ⬝ᵥ v.ofLp = 1 := by
    rw [← X5UH.norm_sq_eq, hv]; simp
  rw [pd_eq, vecMulVec_mul_vecMulVec, h, one_smul]

lemma real_smul_eq (p : ℝ) (Y : Matrix I I ℂ) : (p : ℂ) • Y = p • Y := X5QC.real_smul p Y

/-- cfc on an orthogonal projection -/
lemma cfc_proj {P : Matrix I I ℂ} (hP : P.IsHermitian) (hPP : P * P = P) (f : ℝ → ℝ)
    (hf : f 0 = 0) : cfc f P = ((f 1 : ℝ) : ℂ) • P := by
  have hs : ∀ x ∈ spectrum ℝ P, x = 0 ∨ x = 1 := by
    intro x hx
    have h1 : cfc (fun x : ℝ => x * x) P = cfc (fun x : ℝ => x) P := by
      rw [cfc_mul _ _ _ (X5B2.fin _ _) (X5B2.fin _ _), cfc_id' ℝ P hP.isSelfAdjoint, hPP]
    have := eqOn_of_cfc_eq_cfc h1 (X5B2.fin _ _) (X5B2.fin _ _) hP.isSelfAdjoint hx
    simp only at this
    have h2 : x * (x - 1) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have e : cfc f P = cfc (fun x => f 1 * x) P := by
    refine cfc_congr fun x hx => ?_
    rcases hs x hx with h | h <;> simp [h, hf]
  rw [e, cfc_const_mul _ _ _ (X5B2.fin _ _), cfc_id' ℝ P hP.isSelfAdjoint, real_smul_eq]

lemma pd_herm (v : EuclideanSpace ℂ I) : (QAlgorithms.pureDensity v).IsHermitian := (pd_psd v).1

theorem fid_pure {v w : EuclideanSpace ℂ I} (hv : ‖v‖ = 1) :
    QAlgorithms.rootFidelity (QAlgorithms.pureDensity v) (QAlgorithms.pureDensity w) =
      ‖inner ℂ v w‖ := by
  unfold QAlgorithms.rootFidelity
  set P := QAlgorithms.pureDensity v
  have hP := pd_herm v
  have hPP := pd_idem hv
  rw [cfc_proj hP hPP Real.sqrt Real.sqrt_zero, Real.sqrt_one, Complex.ofReal_one, one_smul]
  set z := inner ℂ v w
  have e : P * QAlgorithms.pureDensity w * P = ((‖z‖ ^ 2 : ℝ) : ℂ) • P := by
    simp only [P, pd_eq, vecMulVec_mul_vecMulVec]
    have h1 : (star v.ofLp ⬝ᵥ w.ofLp) = z := (inner_eq v w).symm
    have h2 : (star w.ofLp ⬝ᵥ v.ofLp) = conj z := by
      rw [← inner_eq, inner_conj_symm]
    rw [h1, smul_dotProduct, h2, smul_eq_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    ext i j
    simp [vecMulVec_apply]
    ring
  rw [e, real_smul_eq, ← cfc_comp_smul _ _ P ((P.finite_real_spectrum.image _).continuousOn _)
    hP.isSelfAdjoint, cfc_proj hP hPP _ (by simp), Matrix.trace_smul, pd_trace, hv]
  simp [Real.sqrt_sq (norm_nonneg z)]

end X5QK
end X5mod_QK_Pure

section X5mod_QK_Main
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5QK
set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma trR_kron (A B : Matrix I I ℂ) : QAlgorithms.traceRight (A ⊗ₖ B) = B.trace • A := by
  ext i j; simp [QAlgorithms.traceRight, Matrix.trace, Finset.mul_sum, mul_comm]

lemma trL_kron (A B : Matrix I I ℂ) : QAlgorithms.traceLeft (A ⊗ₖ B) = A.trace • B := by
  ext i j; simp [QAlgorithms.traceLeft, Matrix.trace, Finset.sum_mul]

lemma mul_isq {X : Matrix I I ℂ} (hX : X.PosSemidef) : X * isq X = cfc Real.sqrt X := by
  have h := congrArg conjTranspose (isq_mul hX)
  rwa [conjTranspose_mul, isq_herm, hX.1.eq, X5B2.sqrt_herm] at h

lemma psd_trace_zero {D : Matrix I I ℂ} (hD : D.PosSemidef) (h : D.trace.re = 0) : D = 0 := by
  rw [← hD.trace_eq_zero_iff, X5UH.psd_tr hD, h, Complex.ofReal_zero]

lemma contr_of {X Y : Matrix I I ℂ} (hX : X.PosSemidef) (hY : (Y - X).PosSemidef)
    (hYs : (1 - isq Y * Y * isq Y).PosSemidef) (hYp : Y.PosSemidef) :
    (1 - isq Y * X * isq Y).PosSemidef := by
  have := hYs.add (conj_psd hY (isq Y) (isq_herm Y))
  convert this using 1
  simp only [Matrix.mul_sub, Matrix.sub_mul]; abel

lemma norm_one_of {M X : Matrix I I ℂ} (hM : Mᴴ * M = X) (hX : X.trace = 1) : ‖vecE M‖ = 1 := by
  have h := norm_vec_sq M
  rw [hM, hX, Complex.one_re] at h
  have h0 := norm_nonneg (vecE M)
  nlinarith [sq_nonneg (‖vecE M‖ - 1), sq_nonneg (‖vecE M‖ + 1)]

lemma low_bound {z1 z2 : ℂ} {t e : ℝ} (h1 : 1 ≤ z1.re) (h2 : ‖z2‖ ≤ t) (ht : t ≤ e) :
    1 - e ≤ ‖z1 - z2‖ := by
  have := norm_sub_norm_le z1 z2
  have := Complex.re_le_norm z1
  linarith

lemma tr_conj_norm (X D : Matrix I I ℂ) (hD : D.IsHermitian) :
    ‖(X * D).trace‖ = ‖(Xᴴ * D).trace‖ := by
  have : (Xᴴ * D).trace = star (X * D).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, hD.eq, Matrix.trace_mul_comm]
  rw [this, norm_star]

theorem coupling [Nonempty I] (rho sigma : Matrix I I ℂ) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : QAlgorithms.IsDensityMatrix sigma)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (hclose : QAlgorithms.traceDistance rho sigma ≤ epsilon) :
    ∃ phi psi theta : EuclideanSpace ℂ (I × I),
    ∃ Theta : Matrix (I × I) (I × I) ℂ,
      ‖phi‖ = 1 ∧ ‖psi‖ = 1 ∧ ‖theta‖ ≤ 1 ∧
      QAlgorithms.traceRight (QAlgorithms.pureDensity phi) = rho ∧
      QAlgorithms.traceLeft (QAlgorithms.pureDensity phi) = rho.transpose ∧
      QAlgorithms.traceRight (QAlgorithms.pureDensity psi) = sigma ∧
      QAlgorithms.traceLeft (QAlgorithms.pureDensity psi) = sigma.transpose ∧
      (rho - QAlgorithms.traceRight (QAlgorithms.pureDensity theta)).PosSemidef ∧
      (sigma.transpose - QAlgorithms.traceLeft (QAlgorithms.pureDensity theta)).PosSemidef ∧
      1 - epsilon ≤ ‖inner ℂ psi theta‖ ∧ 1 - epsilon ≤ ‖inner ℂ phi theta‖ ∧
      QAlgorithms.IsDensityMatrix Theta ∧ QAlgorithms.traceRight Theta = rho ∧
      QAlgorithms.traceLeft Theta = QAlgorithms.traceLeft (QAlgorithms.pureDensity psi) ∧
      1 - epsilon ≤ QAlgorithms.rootFidelity (QAlgorithms.pureDensity psi) Theta ∧
      1 - epsilon ≤ QAlgorithms.rootFidelity (QAlgorithms.pureDensity phi) Theta := by
  obtain ⟨hρ, hρ1⟩ := hrho
  obtain ⟨hσ, hσ1⟩ := hsigma
  set a := cfc Real.sqrt rho
  set s := cfc Real.sqrt sigma
  have ha : aᴴ = a := X5B2.sqrt_herm rho
  have hs : sᴴ = s := X5B2.sqrt_herm sigma
  have haa : a * a = rho := X5B2.sqrt_sq hρ
  have hss : s * s = sigma := X5B2.sqrt_sq hσ
  set H := rho - sigma
  have hH : H.IsHermitian := hρ.1.sub hσ.1
  set P := Hp H
  set N := Hm H
  have hP := Hp_psd H
  have hN := Hm_psd H
  have hHPN : H = P - N := H_eq hH
  set ω := sigma + P
  have hω : ω.PosSemidef := hσ.add hP
  have hωσ : ω - sigma = P := by simp [ω]
  have hωρ : ω - rho = N := by
    have e : ω - rho = P - H := by simp only [ω, H]; abel
    rw [e, hHPN]; abel
  -- the trace distance
  have hTr : P.trace = N.trace := by
    have h := congrArg Matrix.trace hHPN
    rw [Matrix.trace_sub, Matrix.trace_sub, hρ1, hσ1, sub_self] at h
    exact (sub_eq_zero.mp h.symm)
  have htd : QAlgorithms.traceDistance rho sigma = P.trace.re := by
    unfold QAlgorithms.traceDistance
    rw [traceNorm_eq hH, ← hTr]; ring
  have htP : P.trace.re ≤ epsilon := htd ▸ hclose
  have htN : N.trace.re ≤ epsilon := by rw [← hTr]; exact htP
  set w := isq ω
  have hw : wᴴ = w := isq_herm ω
  have hsupp : (1 - w * ω * w).PosSemidef := by rw [isq_conj hω]; exact one_sub_supp hω.1
  have hX : (1 - w * rho * w).PosSemidef := contr_of hρ (by rw [hωρ]; exact hN) hsupp hω
  have hZ : (1 - w * sigma * w).PosSemidef := contr_of hσ (by rw [hωσ]; exact hP) hsupp hω
  set M := a * w * s
  have hMh : Mᴴ = s * w * a := by
    simp only [M, conjTranspose_mul, ha, hw, hs, Matrix.mul_assoc]
  have hMM1 : rho - M * Mᴴ = a * (1 - w * sigma * w) * a := by
    rw [hMh, ← hss, ← haa]
    simp only [M, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hMM2 : sigma - Mᴴ * M = s * (1 - w * rho * w) * s := by
    rw [hMh, ← hss, ← haa]
    simp only [M, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hD1 : (rho - M * Mᴴ).PosSemidef := by rw [hMM1]; exact conj_psd hZ a ha
  have hD2 : (sigma - Mᴴ * M).PosSemidef := by rw [hMM2]; exact conj_psd hX s hs
  have hTM : (Mᴴ * M).trace = ((‖vecE M‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_vec_sq]; exact X5UH.psd_tr (Matrix.posSemidef_conjTranspose_mul_self M)
  set c : ℝ := 1 - ‖vecE M‖ ^ 2
  have hc : 0 ≤ c := by
    have := X5B2.psd_re hD2
    rw [Matrix.trace_sub, hσ1, hTM] at this
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at this
    exact this
  have hθ : ‖vecE M‖ ≤ 1 := by
    have h0 := norm_nonneg (vecE M)
    nlinarith
  have hT1 : (rho - M * Mᴴ).trace = (c : ℂ) := by
    rw [Matrix.trace_sub, hρ1, Matrix.trace_mul_comm, hTM]; simp [c]
  have hT2 : ((sigma - Mᴴ * M)ᵀ).trace = (c : ℂ) := by
    rw [Matrix.trace_transpose, Matrix.trace_sub, hσ1, hTM]; simp [c]
  have key : ∀ D : Matrix I I ℂ, D.PosSemidef → D.trace = (c : ℂ) →
      (((c⁻¹ : ℝ) : ℂ) * c) • D = D := by
    intro D hD hDc
    by_cases h0 : c = 0
    · have : D = 0 := psd_trace_zero hD (by rw [hDc, h0]; simp)
      rw [this, smul_zero]
    · rw [← Complex.ofReal_mul, inv_mul_cancel₀ h0, Complex.ofReal_one, one_smul]
  set Θ := QAlgorithms.pureDensity (vecE M) +
    ((c⁻¹ : ℝ) : ℂ) • ((rho - M * Mᴴ) ⊗ₖ (sigma - Mᴴ * M)ᵀ)
  have hK : (((c⁻¹ : ℝ) : ℂ) • ((rho - M * Mᴴ) ⊗ₖ (sigma - Mᴴ * M)ᵀ)).PosSemidef :=
    (hD1.kronecker hD2.transpose).smul (by exact_mod_cast inv_nonneg.mpr hc)
  have hΘ : Θ.PosSemidef := (pd_psd _).add hK
  have hΘθ : (Θ - QAlgorithms.pureDensity (vecE M)).PosSemidef := by
    simp only [Θ, add_sub_cancel_left]; exact hK
  -- overlaps
  have hψθ : inner ℂ (vecE s) (vecE M) = (a * cfc Real.sqrt ω).trace - (a * w * P).trace := by
    rw [inner_vec, hs, ← Matrix.trace_sub, ← isq_mul hω]
    rw [show a * (isq ω * ω) - a * w * P = a * w * (ω - P) by
      simp only [w, Matrix.mul_sub, Matrix.mul_assoc]]
    rw [show ω - P = s * s by rw [hss]; simp [ω]]
    simp only [M, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm s]
    simp only [Matrix.mul_assoc]
  have hφθ : inner ℂ (vecE a) (vecE M) = (cfc Real.sqrt ω * s).trace - (N * (w * s)).trace := by
    rw [inner_vec, ha, ← Matrix.trace_sub, ← mul_isq hω]
    rw [show ω * isq ω * s - N * (w * s) = (ω - N) * (w * s) by
      simp only [w, Matrix.sub_mul, Matrix.mul_assoc]]
    rw [show ω - N = a * a by rw [haa, ← hωρ]; abel]
    simp only [M, Matrix.mul_assoc]
  have b1 : 1 ≤ (a * cfc Real.sqrt ω).trace.re := by
    have := tr_mono (sq_psd hρ) (X5UH.sqrt_mono hρ (by rw [hωρ]; exact hN))
    rw [haa, hρ1, Complex.one_re] at this; exact this
  have b2 : 1 ≤ (cfc Real.sqrt ω * s).trace.re := by
    have := tr_mono (sq_psd hσ) (X5UH.sqrt_mono hσ (by rw [hωσ]; exact hP))
    rw [hss, hσ1, Complex.one_re, Matrix.trace_mul_comm] at this; exact this
  have b3 : ‖(a * w * P).trace‖ ≤ P.trace.re := by
    rw [tr_conj_norm _ _ hP.1]
    refine abs_tr_contr ?_ hP
    rw [conjTranspose_conjTranspose, conjTranspose_mul, ha, hw]
    convert hX using 2
    rw [← haa]; simp only [Matrix.mul_assoc]
  have b4 : ‖(N * (w * s)).trace‖ ≤ N.trace.re := by
    rw [Matrix.trace_mul_comm]
    refine abs_tr_contr ?_ hN
    rw [conjTranspose_mul, hs, hw]
    convert hZ using 2
    rw [← hss]; simp only [Matrix.mul_assoc]
  have o1 : 1 - epsilon ≤ ‖inner ℂ (vecE s) (vecE M)‖ := by
    rw [hψθ]; exact low_bound b1 b3 htP
  have o2 : 1 - epsilon ≤ ‖inner ℂ (vecE a) (vecE M)‖ := by
    rw [hφθ]; exact low_bound b2 b4 htN
  have nφ : ‖vecE a‖ = 1 := norm_one_of (by rw [ha, haa]) hρ1
  have nψ : ‖vecE s‖ = 1 := norm_one_of (by rw [hs, hss]) hσ1
  refine ⟨vecE a, vecE s, vecE M, Θ, nφ, nψ, hθ, ?_, ?_, ?_, ?_, ?_, ?_, o1, o2, ⟨hΘ, ?_⟩, ?_, ?_,
    ?_, ?_⟩
  · rw [trR_vec, ha, haa]
  · rw [trL_vec, ha, haa]
  · rw [trR_vec, hs, hss]
  · rw [trL_vec, hs, hss]
  · rw [trR_vec]; exact hD1
  · rw [trL_vec, ← Matrix.transpose_sub]; exact hD2.transpose
  · rw [Matrix.trace_add, Matrix.trace_smul, trace_kronecker, hT1, hT2, pd_trace, smul_eq_mul]
    have : ((c⁻¹ : ℝ) : ℂ) * ((c : ℂ) * (c : ℂ)) = c := by
      by_cases h0 : c = 0
      · simp [h0]
      · rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ h0, Complex.ofReal_one, one_mul]
    rw [this]; simp [c]
  · have e1 : ∀ (c' : ℂ) (X : Matrix (I × I) (I × I) ℂ),
        QAlgorithms.traceRight (c' • X) = c' • QAlgorithms.traceRight X := by
      intro c' X; ext i j; simp [QAlgorithms.traceRight, Finset.mul_sum]
    rw [X5UH.tr_add, e1, trR_kron, trR_vec, hT2, smul_smul, key _ hD1 hT1]
    abel
  · have e1 : ∀ (c' : ℂ) (X : Matrix (I × I) (I × I) ℂ),
        QAlgorithms.traceLeft (c' • X) = c' • QAlgorithms.traceLeft X := by
      intro c' X; ext i j; simp [QAlgorithms.traceLeft, Finset.mul_sum]
    have e2 : ∀ (X Y : Matrix (I × I) (I × I) ℂ),
        QAlgorithms.traceLeft (X + Y) = QAlgorithms.traceLeft X + QAlgorithms.traceLeft Y := by
      intro X Y; ext i j; simp [QAlgorithms.traceLeft, Finset.sum_add_distrib]
    rw [e2, e1, trL_kron, trL_vec, trL_vec, hT1, smul_smul, key _ hD2.transpose hT2, hs, hss,
      Matrix.transpose_sub]
    abel
  · exact (fid_pure nψ).symm ▸ o1 |>.trans (X5UH.fid_mono_right (pd_psd _) (pd_psd _) hΘθ)
  · exact (fid_pure nφ).symm ▸ o2 |>.trans (X5UH.fid_mono_right (pd_psd _) (pd_psd _) hΘθ)

end X5QK
end X5mod_QK_Main

section X5mod_AF_Main
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5AF
open X5QC
set_option linter.unusedSectionVars false

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

lemma traceNorm_swap (X Y : Matrix (A × B) (A × B) ℂ) :
    QAlgorithms.traceNorm (Y - X) = QAlgorithms.traceNorm (X - Y) := by
  unfold QAlgorithms.traceNorm
  rw [show Y - X = -(X - Y) by abel, conjTranspose_neg, neg_mul_neg]

lemma bin_eq (q : ℝ) :
    q * Real.logb 2 q + (1 - q) * Real.logb 2 (1 - q) = -(Real.binEntropy q / Real.log 2) := by
  simp only [Real.binEntropy, Real.logb, Real.log_inv]
  ring

lemma sum2 (q : ℝ) (X Y : Matrix (A × B) (A × B) ℂ) :
    ∑ x : Fin 2, ((![q, 1 - q] x : ℝ) : ℂ) • (![X, Y] x) = (q : ℂ) • X + ((1 - q : ℝ) : ℂ) • Y := by
  rw [Fin.sum_univ_two]; rfl

lemma sum2r (q a b : ℝ) : ∑ x : Fin 2, (![q, 1 - q] x) * (![a, b] x) = q * a + (1 - q) * b := by
  simp [Fin.sum_univ_two]

/-- One direction of Winter's bound, in bits. -/
theorem winter_one [Nonempty A] [Nonempty B] {rho sigma : Matrix (A × B) (A × B) ℂ}
    (hr : QAlgorithms.IsDensityMatrix rho) (hs : QAlgorithms.IsDensityMatrix sigma) :
    Hc rho - Hc sigma ≤
      2 * (QAlgorithms.traceNorm (rho - sigma) / 2) * Real.logb 2 (Fintype.card A) +
      (1 + QAlgorithms.traceNorm (rho - sigma) / 2) *
        (Real.binEntropy ((QAlgorithms.traceNorm (rho - sigma) / 2) /
          (1 + QAlgorithms.traceNorm (rho - sigma) / 2)) / Real.log 2) := by
  set H := rho - sigma with hHdef
  have hH : H.IsHermitian := hr.1.1.sub hs.1.1
  set e := QAlgorithms.traceNorm H / 2 with he
  set P := X5QK.Hp H
  set N := X5QK.Hm H
  have hP := X5QK.Hp_psd H
  have hN := X5QK.Hm_psd H
  have hPN : H = P - N := X5QK.H_eq hH
  have htn : QAlgorithms.traceNorm H = P.trace.re + N.trace.re := X5QK.traceNorm_eq hH
  have htr : P.trace.re = N.trace.re := by
    have : H.trace = 0 := by rw [hHdef, Matrix.trace_sub, hr.2, hs.2, sub_self]
    rw [hPN, Matrix.trace_sub] at this
    have := congrArg Complex.re this
    simp only [Complex.sub_re, Complex.zero_re] at this
    linarith
  have hPe : P.trace = (e : ℂ) := by rw [X5UH.psd_tr hP, he, htn, htr]; congr 1; ring
  have hNe : N.trace = (e : ℂ) := by rw [X5UH.psd_tr hN, he, htn, htr]; congr 1; ring
  have he0 : 0 ≤ e := by
    have := hP.trace_nonneg; rw [hPe] at this; exact_mod_cast this
  set L := Real.logb 2 (Fintype.card A)
  rcases he0.lt_or_eq with hpos | hzero
  · -- the main case
    set g : Matrix (A × B) (A × B) ℂ := ((e⁻¹ : ℝ) : ℂ) • P
    set g' : Matrix (A × B) (A × B) ℂ := ((e⁻¹ : ℝ) : ℂ) • N
    have hg : QAlgorithms.IsDensityMatrix g := by
      refine ⟨hP.smul (by exact_mod_cast (inv_pos.2 hpos).le), ?_⟩
      rw [Matrix.trace_smul, hPe, smul_eq_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne']
      simp
    have hg' : QAlgorithms.IsDensityMatrix g' := by
      refine ⟨hN.smul (by exact_mod_cast (inv_pos.2 hpos).le), ?_⟩
      rw [Matrix.trace_smul, hNe, smul_eq_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne']
      simp
    set q : ℝ := 1 / (1 + e)
    have hq0 : 0 < q := by positivity
    have hq1 : q < 1 := by rw [div_lt_one (by linarith)]; linarith
    have hp : ∀ x, 0 ≤ (![q, 1 - q] : Fin 2 → ℝ) x := by
      intro x; fin_cases x <;> simp <;> linarith
    have hsum : ∑ x, (![q, 1 - q] : Fin 2 → ℝ) x = 1 := by simp [Fin.sum_univ_two]
    have hω : (q : ℂ) • rho + ((1 - q : ℝ) : ℂ) • g' = (q : ℂ) • sigma + ((1 - q : ℝ) : ℂ) • g := by
      have hc : ((1 - q : ℝ) : ℂ) * ((e⁻¹ : ℝ) : ℂ) = (q : ℂ) := by
        rw [← Complex.ofReal_mul]; congr 1
        simp only [q]; field_simp; ring
      simp only [g, g', smul_smul, hc, ← smul_add]
      congr 1
      have : rho - sigma = P - N := hPN
      rw [← sub_eq_zero]; rw [← sub_eq_zero] at this
      rw [← this]; abel
    have c1 := Hc_concave (A := A) (B := B) (p := ![q, 1 - q]) (rho := ![rho, g']) hp hsum
      (by intro x; fin_cases x <;> simpa)
    have c2 := Hc_mix (A := A) (B := B) (p := ![q, 1 - q]) (rho := ![sigma, g]) hp hsum
      (by intro x; fin_cases x <;> simpa)
    rw [sum2] at c1 c2
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at c1 c2
    rw [bin_eq, ← hω] at c2
    rw [show (1 : ℝ) - q = e / (1 + e) by simp only [q]; field_simp; ring] at c1 c2
    have hb : Real.binEntropy q = Real.binEntropy (e / (1 + e)) := by
      rw [← Real.binEntropy_one_sub]; congr 1; simp only [q]; field_simp; ring
    rw [hb] at c2
    have b1 := Hc_le hg
    have b2 := Hc_ge hg'
    have hq' : q * (1 + e) = 1 := by simp only [q]; field_simp
    have key : q * (Hc rho - Hc sigma) ≤ (e / (1 + e)) * (2 * L) +
        Real.binEntropy (e / (1 + e)) / Real.log 2 := by
      have : (e / (1 + e)) * (Hc g - Hc g') ≤ (e / (1 + e)) * (2 * L) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    have := mul_le_mul_of_nonneg_left key (by linarith : (0 : ℝ) ≤ 1 + e)
    have e2 : (1 + e) * (e / (1 + e)) = e := by field_simp
    rw [← mul_assoc, mul_comm (1 + e) q, hq', one_mul, mul_add, ← mul_assoc, e2] at this
    linarith
  · -- e = 0 : rho = sigma
    have hP0 : P = 0 := X5QK.psd_trace_zero hP (by rw [hPe, ← hzero]; simp)
    have hN0 : N = 0 := X5QK.psd_trace_zero hN (by rw [hNe, ← hzero]; simp)
    have : rho = sigma := by
      have h' : rho - sigma = 0 := by rw [← hHdef, hPN, hP0, hN0, sub_zero]
      exact sub_eq_zero.1 h'
    rw [this, ← hzero]; simp

theorem winter [Nonempty A] [Nonempty B] (rho sigma : Matrix (A × B) (A × B) ℂ)
    (hr : QAlgorithms.IsDensityMatrix rho) (hs : QAlgorithms.IsDensityMatrix sigma) :
    |Real.log 2 * Hc rho - Real.log 2 * Hc sigma| ≤
      2 * (QAlgorithms.traceNorm (rho - sigma) / 2) * Real.log (Fintype.card A) +
      (1 + QAlgorithms.traceNorm (rho - sigma) / 2) *
        Real.binEntropy ((QAlgorithms.traceNorm (rho - sigma) / 2) /
          (1 + QAlgorithms.traceNorm (rho - sigma) / 2)) := by
  have h1 := winter_one hr hs
  have h2 := winter_one hs hr
  rw [traceNorm_swap] at h2
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have eL : Real.log 2 * Real.logb 2 (Fintype.card A) = Real.log (Fintype.card A) := by
    rw [Real.logb]; field_simp
  set e := QAlgorithms.traceNorm (rho - sigma) / 2
  set b := Real.binEntropy (e / (1 + e))
  have k1 := mul_le_mul_of_nonneg_left h1 hl.le
  have k2 := mul_le_mul_of_nonneg_left h2 hl.le
  have r : Real.log 2 * (2 * e * Real.logb 2 (Fintype.card A) + (1 + e) * (b / Real.log 2)) =
      2 * e * Real.log (Fintype.card A) + (1 + e) * b := by
    rw [← eL]; field_simp
  rw [r] at k1 k2
  rw [abs_le]; constructor <;> nlinarith

end X5AF
end X5mod_AF_Main

section X5mod_AF_Fannes

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms

namespace X5AF

lemma nml_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : Real.log y ≤ -1) :
    -x * Real.log x ≤ -y * Real.log y := by
  have hy0 : 0 < y := by
    rcases (hx.trans hxy).lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hy; norm_num at hy
  rcases hx.lt_or_eq with hx0 | hx0
  · have h1 := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at h1
    have h2 : x * (Real.log y - Real.log x) ≤ y - x := by
      have e : x * (y / x - 1) = y - x := by field_simp
      have := mul_le_mul_of_nonneg_left h1 hx0.le
      rw [e] at this; exact this
    nlinarith
  · rw [← hx0]; simp; nlinarith

lemma bin_scaled {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) * Real.binEntropy (t / (1 + t)) = (1 + t) * Real.log (1 + t) - t * Real.log t := by
  rcases ht.lt_or_eq with h | h
  · have h1 : (0 : ℝ) < 1 + t := by linarith
    unfold Real.binEntropy
    rw [show 1 - t / (1 + t) = 1 / (1 + t) by field_simp; ring, inv_div, one_div, inv_inv,
      Real.log_div h1.ne' h.ne']
    field_simp
    ring
  · rw [← h]; simp

lemma log_six : Real.log 6 ≤ 2 * Real.log 2 + 1 / 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  have e : Real.log 6 = 2 * Real.log 2 + Real.log (3 / 2) := by
    rw [show (6 : ℝ) = 2 * 2 * (3 / 2) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]; ring
  rw [e]; linarith

lemma log_le_neg_one {y : ℝ} (hy0 : 0 < y) (hy : y ≤ 1 / 4) : Real.log y ≤ -1 := by
  have h1 : Real.log y ≤ Real.log (1 / 4) := Real.log_le_log hy0 hy
  have h2 : Real.log (1 / 4) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have := Real.log_two_gt_d9
  linarith

/-- the scalar inequality behind the Fannes-type bound -/
lemma scalar_fannes {t ε : ℝ} (ht : 0 ≤ t) (hte : t ≤ ε / 2) :
    (1 + t) * Real.binEntropy (t / (1 + t)) / Real.log 2 ≤
      QAlgorithms.Papers.Independent.Gap48.P32.fannesEta (2 * ε) + 2 * ε := by
  have hl := Real.log_two_gt_d9
  have hl0 : 0 < Real.log 2 := by linarith
  have ha : Real.log (1 + t) ≤ t := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + t)]
  have hal : (1 + t) * Real.log (1 + t) ≤ (1 + t) * t := mul_le_mul_of_nonneg_left ha (by linarith)
  unfold QAlgorithms.Papers.Independent.Gap48.P32.fannesEta
  split_ifs with h
  · -- 2ε ≤ 1/4
    rw [bin_scaled ht, div_le_iff₀ hl0]
    rcases (show (0 : ℝ) ≤ 2 * ε by linarith).lt_or_eq with h2 | h2
    · have m := nml_mono ht (by linarith : t ≤ 2 * ε) (log_le_neg_one h2 h)
      have e : -(2 * ε) * Real.logb 2 (2 * ε) * Real.log 2 = -(2 * ε) * Real.log (2 * ε) := by
        rw [Real.logb]; field_simp
      have e2 : (-(2 * ε) * Real.logb 2 (2 * ε) + 2 * ε) * Real.log 2 =
          -(2 * ε) * Real.log (2 * ε) + 2 * ε * Real.log 2 := by rw [add_mul, e]
      rw [e2]
      nlinarith
    · have : t = 0 := by linarith
      subst this; rw [← h2]; simp
  · push_neg at h
    rw [div_le_iff₀ hl0]
    by_cases h3 : ε < 1 / 3
    · rw [bin_scaled ht]
      have ht6 : t ≤ 1 / 6 := by linarith
      have m := nml_mono ht ht6 (by
        rw [one_div, Real.log_inv]
        have := log_six
        have h6 : 1 < Real.log 6 := by
          rw [Real.lt_log_iff_exp_lt (by norm_num)]
          have := Real.exp_one_lt_d9; linarith
        linarith)
      have e6 : -(1 / 6 : ℝ) * Real.log (1 / 6) = Real.log 6 / 6 := by
        rw [one_div, Real.log_inv]; ring
      rw [e6] at m
      have := log_six
      nlinarith
    · push_neg at h3
      have hb : Real.binEntropy (t / (1 + t)) ≤ Real.log 2 := Real.binEntropy_le_log_two
      nlinarith

theorem fannes_gen {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B] {rho sigma : Matrix (A × B) (A × B) ℂ}
    (hr : IsDensityMatrix rho) (hs : IsDensityMatrix sigma) {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : traceNorm (rho - sigma) ≤ ε) :
    |Hc rho - Hc sigma| ≤
      QAlgorithms.Papers.Independent.Gap48.P32.fannesEta (2 * ε) +
        3 * ε * Real.logb 2 (Fintype.card A) := by
  have hη : 0 ≤ QAlgorithms.Papers.Independent.Gap48.P32.fannesEta (2 * ε) := by
    unfold QAlgorithms.Papers.Independent.Gap48.P32.fannesEta
    split_ifs with h
    · have : Real.logb 2 (2 * ε) ≤ 0 := Real.logb_nonpos one_lt_two (by linarith) (by linarith)
      nlinarith
    · norm_num
  have hcard : 1 ≤ Fintype.card A := Fintype.card_pos
  rcases hcard.lt_or_eq with h2 | h1
  · -- card A ≥ 2
    have hL : 1 ≤ Real.logb 2 (Fintype.card A) := by
      rw [Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast Fintype.card_pos)]
      simp; exact_mod_cast h2
    have h1 := winter_one hr hs
    have h2' := winter_one hs hr
    rw [traceNorm_swap] at h2'
    set t := traceNorm (rho - sigma) / 2
    have ht0 : 0 ≤ t := by
      have : 0 ≤ traceNorm (rho - sigma) := by
        rw [X5QK.traceNorm_eq (hr.1.1.sub hs.1.1)]
        have a' := (Complex.le_def.1 (X5QK.Hp_psd (rho - sigma)).trace_nonneg).1
        have b' := (Complex.le_def.1 (X5QK.Hm_psd (rho - sigma)).trace_nonneg).1
        simp at a' b'
        linarith
      simp only [t]; linarith
    have hte : t ≤ ε / 2 := by simp only [t]; linarith
    have k := scalar_fannes ht0 hte
    have k2 : 2 * t * Real.logb 2 (Fintype.card A) ≤ ε * Real.logb 2 (Fintype.card A) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have k3 : 2 * ε ≤ 2 * ε * Real.logb 2 (Fintype.card A) := by nlinarith
    have k' : (1 + t) * (Real.binEntropy (t / (1 + t)) / Real.log 2) ≤
        QAlgorithms.Papers.Independent.Gap48.P32.fannesEta (2 * ε) + 2 * ε := by
      rw [mul_div_assoc']; exact k
    rw [abs_le]; constructor
    · linarith
    · linarith
  · -- card A = 1 : conditional entropies vanish
    have e : Real.logb 2 (Fintype.card A) = 0 := by rw [← h1]; simp
    have a1 := Hc_le hr; have a2 := Hc_ge hr; have a3 := Hc_le hs; have a4 := Hc_ge hs
    rw [e] at a1 a2 a3 a4
    rw [e, show Hc rho - Hc sigma = 0 by linarith]; simpa using hη

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

lemma vn_sub {X : Matrix m m ℂ} (hX : X.IsHermitian) (e : n ≃ m) :
    QAlgorithms.vnEntropy (X.submatrix e e) = QAlgorithms.vnEntropy X := by
  rw [vn_eq, vn_eq]; unfold T; rw [tr_cfc_sub hX]

lemma traceNorm_sub (Z : Matrix m m ℂ) (e : n ≃ m) :
    QAlgorithms.traceNorm (Z.submatrix e e) = QAlgorithms.traceNorm Z := by
  unfold QAlgorithms.traceNorm
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    tr_cfc_sub (Matrix.isHermitian_conjTranspose_mul_self Z)]

lemma dens_sub {X : Matrix m m ℂ} (hX : QAlgorithms.IsDensityMatrix X) (e : n ≃ m) :
    QAlgorithms.IsDensityMatrix (X.submatrix e e) :=
  ⟨hX.1.submatrix e, (trace_sub_equiv e X).trans hX.2⟩

/-- two-sided Winter bound in bits -/
theorem winter_abs {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B] {rho sigma : Matrix (A × B) (A × B) ℂ}
    (hr : QAlgorithms.IsDensityMatrix rho) (hs : QAlgorithms.IsDensityMatrix sigma) :
    |Hc rho - Hc sigma| ≤
      2 * (QAlgorithms.traceNorm (rho - sigma) / 2) * Real.logb 2 (Fintype.card A) +
      (1 + QAlgorithms.traceNorm (rho - sigma) / 2) *
        (Real.binEntropy ((QAlgorithms.traceNorm (rho - sigma) / 2) /
          (1 + QAlgorithms.traceNorm (rho - sigma) / 2)) / Real.log 2) := by
  have h1 := winter_one hr hs
  have h2 := winter_one hs hr
  rw [traceNorm_swap] at h2
  rw [abs_le]; constructor <;> linarith

lemma traceNorm_nonneg {Z : Matrix m m ℂ} (hZ : Z.IsHermitian) : 0 ≤ QAlgorithms.traceNorm Z := by
  rw [X5QK.traceNorm_eq hZ]
  have a' := (Complex.le_def.1 (X5QK.Hp_psd Z).trace_nonneg).1
  have b' := (Complex.le_def.1 (X5QK.Hm_psd Z).trace_nonneg).1
  simp at a' b'
  linarith

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

/-- quantum Pinsker inequality `‖ρ - σ‖₁² ≤ 2 D(ρ‖σ)` (nats) under the domination `c ρ ≤ σ` -/
theorem pinsker {H : Type*} [Fintype H] [DecidableEq H] [Nonempty H] {ρ σ : Matrix H H ℂ}
    (hρ : QAlgorithms.IsDensityMatrix ρ) (hσ : QAlgorithms.IsDensityMatrix σ) {c : ℝ}
    (hc : 0 < c) (hdom : (σ - ((c : ℝ) : ℂ) • ρ).PosSemidef) :
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
    have h := (hdom.conjTranspose_mul_mul_same U).diag_nonneg (i := j)
    rw [← Matrix.star_eq_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, hsd] at h
    have h' := (Complex.nonneg_iff.1 h).1
    simp [hj, r, Complex.mul_re] at h'
    have := hr0 j
    nlinarith
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
end X5mod_PK_Supp

section X5mod_PK_Coh
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma sum_pin (ρ : Matrix n n ℂ) :
    ∑ θ : Sg n, diagonal (sgn θ) * ρ * diagonal (sgn θ) =
      (Fintype.card (Sg n) : ℂ) • diagonal (fun i => ρ i i) := by
  ext i j
  simp only [Matrix.sum_apply, mul_diagonal, diagonal_mul, Matrix.smul_apply, diagonal_apply,
    smul_eq_mul]
  have : ∀ θ : Sg n, sgn θ i * ρ i j * sgn θ j = ρ i j * (sgn θ i * sgn θ j) := fun θ => by ring
  rw [Finset.sum_congr rfl fun θ _ => this θ, ← Finset.mul_sum, sum_sgn]
  by_cases h : i = j
  · subst h; simp [mul_comm]
  · simp [h]

lemma sgn_one : diagonal (sgn (fun _ : n => true)) = 1 := by
  ext i j; by_cases h : i = j <;> simp [sgn, diagonal_apply, Matrix.one_apply, h]

lemma diag_herm_sgn (θ : Sg n) : (diagonal (sgn θ))ᴴ = diagonal (sgn θ) := by
  rw [diagonal_conjTranspose]; congr 1; ext i; simp [star_sgn]

/-- the dephased state dominates `ρ / N` -/
lemma dom_pin {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (diagonal (fun i => ρ i i) -
      (((Fintype.card (Sg n) : ℝ)⁻¹ : ℝ) : ℂ) • ρ).PosSemidef := by
  have hN : (Fintype.card (Sg n) : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_pos).ne'
  have e : diagonal (fun i => ρ i i) - (((Fintype.card (Sg n) : ℝ)⁻¹ : ℝ) : ℂ) • ρ =
      (((Fintype.card (Sg n) : ℝ)⁻¹ : ℝ) : ℂ) •
        ∑ θ ∈ Finset.univ.erase (fun _ : n => true), diagonal (sgn θ) * ρ * diagonal (sgn θ) := by
    have h1 := sum_pin ρ
    rw [← Finset.add_sum_erase _ _ (mem_univ (fun _ : n => true)), sgn_one, Matrix.one_mul,
      Matrix.mul_one] at h1
    have h2 : diagonal (fun i => ρ i i) = (((Fintype.card (Sg n) : ℝ)⁻¹ : ℝ) : ℂ) •
        (ρ + ∑ θ ∈ Finset.univ.erase (fun _ : n => true), diagonal (sgn θ) * ρ * diagonal (sgn θ)) := by
      rw [h1, smul_smul]; push_cast; rw [inv_mul_cancel₀ hN, one_smul]
    rw [h2, smul_add, add_sub_cancel_left]
  rw [e]
  refine Matrix.PosSemidef.smul ?_ (by positivity)
  refine Matrix.posSemidef_sum _ fun θ _ => ?_
  have := hρ.mul_mul_conjTranspose_same (diagonal (sgn θ))
  rwa [diag_herm_sgn] at this

lemma ker_of_dom {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) {c : ℝ} (hc : 0 < c)
    (h : (σ - ((c : ℝ) : ℂ) • ρ).PosSemidef) :
    LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  rw [← hρ.dotProduct_mulVec_zero_iff]
  have h1 := h.dotProduct_mulVec_nonneg v
  rw [Matrix.sub_mulVec, dotProduct_sub, hv, dotProduct_zero, zero_sub, Matrix.smul_mulVec,
    dotProduct_smul] at h1
  have h2 := hρ.dotProduct_mulVec_nonneg v
  have h3 : ((c : ℝ) : ℂ) • (star v ⬝ᵥ ρ *ᵥ v) ≤ 0 := by
    have := neg_nonneg.1 h1; simpa using this
  rw [smul_eq_mul] at h3
  have hz := Complex.nonneg_iff.1 h2
  have h3' := (Complex.le_def.1 h3).1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.zero_re] at h3'
  apply Complex.ext
  · simp only [Complex.zero_re]; nlinarith [hz.1]
  · simp only [Complex.zero_im]; exact hz.2.symm

lemma tr_mul_log_diag (ρ : Matrix n n ℂ) (q : n → ℝ) :
    (ρ * cfc Real.log (diagonal (fun i => ((q i : ℝ) : ℂ)))).trace.re =
      ∑ i, (ρ i i).re * Real.log (q i) := by
  rw [cfc_diag, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_diagonal, Complex.mul_re]

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

section X5mod_PK_CohMain
open Matrix Finset Polynomial
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

namespace X5PK
open X5QC
set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma diag_real {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    diagonal (fun i => ρ i i) = diagonal (fun i => (((ρ i i).re : ℝ) : ℂ)) := by
  congr 1; ext i; exact (hρ.coe_re_apply_self i).symm

lemma dephase_dens {ρ : Matrix n n ℂ} (hρ : QAlgorithms.IsDensityMatrix ρ) :
    QAlgorithms.IsDensityMatrix (diagonal (fun i => ρ i i)) := by
  have h := dom_pin hρ.1
  refine ⟨?_, ?_⟩
  · have hc : (0 : ℝ) ≤ ((Fintype.card (Sg n) : ℝ)⁻¹) := by positivity
    have := h.add (hρ.1.smul (a := (((Fintype.card (Sg n) : ℝ)⁻¹ : ℝ) : ℂ)) (by exact_mod_cast hc))
    simpa using this
  · rw [Matrix.trace_diagonal, ← hρ.2]; rfl

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

/-- relative entropy of coherence: the real-valued facts -/
theorem coh_main [Nonempty n] {ρ : Matrix n n ℂ} (hρ : QAlgorithms.IsDensityMatrix ρ) :
    0 ≤ T ρ - T (diagonal (fun i => ρ i i)) ∧
    (cfc (fun x : ℝ => x * Real.log x) ρ - ρ * cfc Real.log (diagonal (fun i => ρ i i))).trace.re =
      T ρ - T (diagonal (fun i => ρ i i)) ∧
    ∀ δ : Matrix n n ℂ, QAlgorithms.IsDensityMatrix δ → (∀ i j, i ≠ j → δ i j = 0) →
      LinearMap.ker δ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin →
      T ρ - T (diagonal (fun i => ρ i i)) ≤
        (cfc (fun x : ℝ => x * Real.log x) ρ - ρ * cfc Real.log δ).trace.re := by
  have hH := hρ.1.isHermitian
  set p : n → ℝ := fun i => (ρ i i).re
  have hΔ : diagonal (fun i => ρ i i) = diagonal (fun i => ((p i : ℝ) : ℂ)) := diag_real hH
  have hTΔ : T (diagonal (fun i => ρ i i)) = ∑ i, p i * Real.log (p i) := by
    unfold T; rw [hΔ, cfc_diag, trace_diagonal, Complex.re_sum]; simp
  have hD : ∀ q : n → ℝ, (cfc (fun x : ℝ => x * Real.log x) ρ -
      ρ * cfc Real.log (diagonal (fun i => ((q i : ℝ) : ℂ)))).trace.re =
      T ρ - ∑ i, p i * Real.log (q i) := fun q => by
    rw [Matrix.trace_sub, Complex.sub_re, tr_mul_log_diag]; rfl
  have h2 : (cfc (fun x : ℝ => x * Real.log x) ρ -
      ρ * cfc Real.log (diagonal (fun i => ρ i i))).trace.re =
      T ρ - T (diagonal (fun i => ρ i i)) := by
    rw [hTΔ, hΔ, hD]
  refine ⟨?_, h2, ?_⟩
  · have hc : (0 : ℝ) < ((Fintype.card (Sg n) : ℝ)⁻¹) := by
      have : 0 < Fintype.card (Sg n) := Fintype.card_pos
      positivity
    have hp := pinsker hρ (dephase_dens hρ) hc (dom_pin hρ.1)
    rw [relEnt_def, mul_log _ hH, h2] at hp
    nlinarith [sq_nonneg (QAlgorithms.traceNorm (ρ - diagonal fun i => ρ i i))]
  · intro δ hδ hdiag hker
    set q : n → ℝ := fun i => (δ i i).re
    have hδe : δ = diagonal (fun i => ((q i : ℝ) : ℂ)) := by
      rw [← diag_real hδ.1.isHermitian]
      ext i j; by_cases h : i = j
      · subst h; simp
      · simp [h, hdiag i j h]
    have hq0 : ∀ i, 0 ≤ q i := fun i => (Complex.nonneg_iff.1 (hδ.1.diag_nonneg (i := i))).1
    have hp0 : ∀ i, 0 ≤ p i := fun i => (Complex.nonneg_iff.1 (hρ.1.diag_nonneg (i := i))).1
    have hsupp : ∀ i, q i = 0 → p i = 0 := fun i hi => by
      have : δ i i = 0 := by
        rw [← hδ.1.isHermitian.coe_re_apply_self i]; simp [q] at hi; simp [hi]
      simp [p, ker_single hker hdiag i this]
    have hsum : ∀ X : Matrix n n ℂ, X.trace = 1 → ∑ i, (X i i).re = 1 := fun X h => by
      rw [← Complex.re_sum]; change (X.trace).re = 1; rw [h]; simp
    have hkl := kl_nonneg' p q hp0 hq0 hsupp (hsum ρ hρ.2) (hsum δ hδ.2)
    rw [hδe, hD, hTΔ]
    rw [Finset.sum_sub_distrib] at hkl
    linarith

end X5PK
end X5mod_PK_CohMain

section X5mod_PK_CohAll

end X5mod_PK_CohAll

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P04


theorem solution (d : ℕ) (hd : 0 < d) (rho : CoherenceMatrix d)
    (hrho : IsDensityMatrix rho) :
    0 ≤ entropyCoherence d rho ∧
    ∃ hdiag : IsDensityMatrix (dephasedMatrix rho),
      IncoherentState (dephasedMatrix rho) ∧
      QuantumLoss.umegakiEntropy rho (dephasedMatrix rho) hrho hdiag =
        ENNReal.ofReal (entropyCoherence d rho) ∧
      ∀ delta, ∀ hdelta : IsDensityMatrix delta, BasisDiagonal delta →
        ENNReal.ofReal (entropyCoherence d rho) ≤
          QuantumLoss.umegakiEntropy rho delta hrho hdelta := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨h0, h1, h2⟩ := X5PK.coh_main hrho
  have hC : entropyCoherence d rho =
      X5QC.T rho - X5QC.T (Matrix.diagonal (fun i => rho i i)) := by
    unfold entropyCoherence naturalEntropy dephasedMatrix
    rw [X5QC.vn_eq, X5QC.vn_eq]
    have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    field_simp
    ring
  have hdiag : IsDensityMatrix (dephasedMatrix rho) := X5PK.dephase_dens hrho
  have hker : LinearMap.ker (dephasedMatrix rho).mulVecLin ≤ LinearMap.ker rho.mulVecLin := by
    have hc : (0 : ℝ) < ((Fintype.card (X5PK.Sg (Fin d)) : ℝ)⁻¹) := by
      have : 0 < Fintype.card (X5PK.Sg (Fin d)) := Fintype.card_pos
      positivity
    exact X5PK.ker_of_dom hrho.1 hc (X5PK.dom_pin hrho.1)
  refine ⟨hC ▸ h0, hdiag, ⟨hdiag, fun i j h => by simp [dephasedMatrix, h]⟩, ?_, ?_⟩
  · unfold QuantumLoss.umegakiEntropy
    rw [if_pos hker, hC]
    congr 1
  · intro delta hdelta hbd
    unfold QuantumLoss.umegakiEntropy
    split_ifs with hk
    · rw [hC]
      exact ENNReal.ofReal_le_ofReal (h2 delta hdelta hbd hk)
    · exact le_top
