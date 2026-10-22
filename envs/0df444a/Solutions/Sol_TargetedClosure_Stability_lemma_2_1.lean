-- Prove2me | solution 1 for TargetedClosure.Stability.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T20:52:19.00237+00:00
-- url     : https://prove2.me/submissions/88e2c268-1c08-4e3d-af94-53cd0dfcea8a

import Mathlib
import Definitions.Def_TargetedClosure_Stability_Model

set_option autoImplicit false

namespace TCS23664385

open Matrix TargetedClosure.Stability

variable {n : ℕ}

lemma thr_pos (P : Params n) (hP : P.Standing) : 0 < thr P := by
  obtain ⟨-, -, -, hβ, hκ, hγ, hμ, -, -, -, -, hs⟩ := hP
  unfold thr
  positivity

lemma Vinv_eq (P : Params n) (hP : P.Standing) : (Vmat P)⁻¹ = Vinv P := by
  obtain ⟨-, -, -, hβ, hκ, hγ, hμ, -, -, -, -, hs⟩ := hP
  have ha : P.μ + P.κ ≠ 0 := by positivity
  have hb : P.μ + P.γ ≠ 0 := by positivity
  apply Matrix.inv_eq_right_inv
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three, Vmat, Vinv,
    Matrix.one_apply, Prod.mk.injEq]
  by_cases h : i2 = j2
  · subst h
    fin_cases i1 <;> fin_cases j1 <;> simp [Finset.sum_ite_eq'] <;>
      field_simp <;> ring
  · fin_cases i1 <;> fin_cases j1 <;> simp [h, Finset.sum_ite_eq']

lemma M_row (P : Params n) (x : Fin n → ℝ) (p q : Idx n) (hp : p.1 ≠ 0) :
    (Fmat P x * Vinv P) p q = 0 := by
  simp [Matrix.mul_apply, Fmat, hp]

lemma M_00 (P : Params n) (hP : P.Standing) (x : Fin n → ℝ) (i j : Fin n) :
    (Fmat P x * Vinv P) (0, i) (0, j) = (1 / thr P) * Fbar P x i j := by
  obtain ⟨-, -, -, hβ, hκ, hγ, hμ, -, -, -, -, hs⟩ := hP
  have ha : P.μ + P.κ ≠ 0 := by positivity
  have hb : P.μ + P.γ ≠ 0 := by positivity
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three, Fmat, Vinv, Fbar, thr]
  simp [Finset.sum_ite_eq']
  field_simp


/-- The matrix `T X Λ Tᵀ`. -/
noncomputable def Kmat (P : Params n) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Tmat P * Xmat x * Lam P * (Tmat P).transpose

lemma K_apply (P : Params n) (x : Fin n → ℝ) (i j : Fin n) :
    Kmat P x i j = ∑ k, P.tau i k * x k * (1 / mixMass P k) * P.tau j k := by
  rw [Kmat, Matrix.mul_apply]
  simp [Matrix.mul_diagonal, Xmat, Lam, Tmat]

lemma Fbar_eq (P : Params n) (x : Fin n → ℝ) (i j : Fin n) :
    Fbar P x i j = P.N i * Kmat P x i j := by
  rw [K_apply]; unfold Fbar; congr 1
  apply Finset.sum_congr rfl; intro k _; ring

lemma K_symm (P : Params n) (x : Fin n → ℝ) (i j : Fin n) :
    Kmat P x i j = Kmat P x j i := by
  rw [K_apply, K_apply]; apply Finset.sum_congr rfl; intro k _; ring

lemma K_psd (P : Params n) (hP : P.Standing) (x : Fin n → ℝ) (hx : IsActivity x) :
    (Kmat P x).PosSemidef := by
  obtain ⟨hN, ht, -⟩ := hP
  have hd : (0 : Fin n → ℝ) ≤ fun k => x k * (1 / mixMass P k) := by
    intro k
    have : 0 ≤ mixMass P k := Finset.sum_nonneg fun l _ => mul_nonneg (hN l).le (ht l k)
    exact mul_nonneg (hx k).1 (one_div_nonneg.2 this)
  have hK : Kmat P x = Tmat P * diagonal (fun k => x k * (1 / mixMass P k)) * (Tmat P)ᴴ := by
    rw [Kmat, conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc (Tmat P), Xmat, Lam,
      diagonal_mul_diagonal]
  rw [hK]
  exact (PosSemidef.diagonal hd).mul_mul_conjTranspose_same _

lemma Dinv (P : Params n) (hP : P.Standing) : (Nhat P)⁻¹ = diagonal (fun i => 1 / P.N i) := by
  obtain ⟨hN, -⟩ := hP
  apply Matrix.inv_eq_left_inv
  rw [Nhat, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; have := (hN i).ne'; field_simp

/-- extension of a vector on block 0 -/
def extv (u : Fin n → ℂ) : Idx n → ℂ := fun p => if p.1 = 0 then u p.2 else 0

lemma Mc_ext (P : Params n) (hP : P.Standing) (x : Fin n → ℝ) (u : Fin n → ℂ) (p : Idx n) :
    (((Fmat P x * Vinv P).map (algebraMap ℝ ℂ)) *ᵥ extv u) p =
      if p.1 = 0 then ((1 / thr P : ℝ) : ℂ) * ∑ j, (Fbar P x p.2 j : ℂ) * u j else 0 := by
  rcases p with ⟨p1, i⟩
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three, extv, map_apply]
  by_cases h : p1 = 0
  · subst h
    simp [M_00 P hP, Finset.mul_sum, mul_assoc]
  · simp [M_row P x (p1, i) _ h, h]

lemma mem_spec {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) (z : ℂ) :
    z ∈ spectrum ℂ B ↔ ∃ w ≠ 0, B *ᵥ w = z • w := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff]
  refine exists_congr fun w => and_congr_right fun _ => ?_
  rw [sub_mulVec, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec, sub_eq_zero, eq_comm]

lemma sup_lt (S : Set ℂ) (hS : S.Finite) (h : ∀ z ∈ S, ‖z‖ < 1) :
    (⨆ z ∈ S, (‖z‖₊ : ENNReal)) < 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨z0, hz0, hmax⟩ := Set.exists_max_image S (fun z => ‖z‖₊) hS hne
  calc (⨆ z ∈ S, (‖z‖₊ : ENNReal)) ≤ ‖z0‖₊ :=
        iSup₂_le fun z hz => by exact_mod_cast hmax z hz
    _ < 1 := by
        have := h z0 hz0
        rw [ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe, coe_nnnorm]
        simpa using this

lemma quad_split (B : Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i j, B i j = B j i) (u : Fin n → ℂ) :
    (∑ i, (starRingEnd ℂ) (u i) * ∑ j, (B i j : ℂ) * u j) =
      (((fun i => (u i).re) ⬝ᵥ (B *ᵥ fun i => (u i).re)) +
        ((fun i => (u i).im) ⬝ᵥ (B *ᵥ fun i => (u i).im)) : ℝ) := by
  apply Complex.ext
  · simp only [Complex.re_sum, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, dotProduct, mulVec,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  · simp only [Complex.im_sum, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, Finset.mul_sum]
    have key : ∑ i, ∑ j, (u i).im * (B i j * (u j).re) =
        ∑ i, ∑ j, (u i).re * (B i j * (u j).im) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
      rw [hB]; ring
    simp only [Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib, zero_mul, add_zero,
      zero_add]
    have e : ∑ x, ∑ y, (u x).im * ((B x y : ℂ) * u y).re =
        ∑ x, ∑ y, (u x).im * (B x y * (u y).re) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [Complex.re_ofReal_mul]
    rw [e, key]; ring

lemma qA_eq (P : Params n) (hP : P.Standing) (x : Fin n → ℝ) (y : Fin n → ℝ) :
    y ⬝ᵥ ((thr P • (Nhat P)⁻¹ - Kmat P x) *ᵥ y) =
      thr P * ∑ i, y i ^ 2 / P.N i - y ⬝ᵥ (Kmat P x *ᵥ y) := by
  rw [Dinv P hP, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  congr 2
  simp only [dotProduct, mulVec_diagonal]
  apply Finset.sum_congr rfl; intro i _; ring

lemma backward (P : Params n) (hP : P.Standing) (x : Fin n → ℝ) (hx : IsActivity x)
    (hA : (thr P • (Nhat P)⁻¹ - Kmat P x).PosDef) (z : ℂ)
    (hz : z ∈ spectrum ℂ ((Fmat P x * Vinv P).map (algebraMap ℝ ℂ))) : ‖z‖ < 1 := by
  have hthr := thr_pos P hP
  have hN := hP.1
  obtain ⟨v, hv0, hv⟩ := (mem_spec _ _).1 hz
  by_cases hz0 : z = 0
  · simp [hz0]
  have hrow : ∀ p : Idx n, p.1 ≠ 0 → v p = 0 := by
    intro p hp
    have h1 := congrFun hv p
    have h2 : (((Fmat P x * Vinv P).map (algebraMap ℝ ℂ)) *ᵥ v) p = 0 := by
      simp [mulVec, dotProduct, M_row P x p _ hp]
    rw [h2, Pi.smul_apply, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left hz0
  set u : Fin n → ℂ := fun j => v (0, j) with hu
  have hvu : v = extv u := by
    funext ⟨p1, j⟩
    by_cases h : p1 = 0
    · subst h; simp [extv, u]
    · simp [extv, h, hrow (p1, j) h]
  have hu0 : u ≠ 0 := by
    intro h; apply hv0; rw [hvu, h]; funext p; simp [extv]
  have hT : (thr P : ℂ) ≠ 0 := by exact_mod_cast hthr.ne'
  have heig : ∀ i, ∑ j, (Kmat P x i j : ℂ) * u j = (z * thr P) * (u i / P.N i) := by
    intro i
    have hNi : (P.N i : ℂ) ≠ 0 := by exact_mod_cast (hN i).ne'
    have h1 := congrFun hv (0, i)
    rw [hvu, Mc_ext P hP x u (0, i)] at h1
    simp only [extv, Pi.smul_apply, smul_eq_mul] at h1
    rw [if_pos trivial, if_pos trivial] at h1
    have hF : ∑ j, (Fbar P x i j : ℂ) * u j = (P.N i : ℂ) * ∑ j, (Kmat P x i j : ℂ) * u j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fbar_eq]; push_cast; ring
    rw [hF] at h1
    have e1 : ∑ j, (Kmat P x i j : ℂ) * u j =
        (((1 / thr P : ℝ) : ℂ) * ((P.N i : ℂ) * ∑ j, (Kmat P x i j : ℂ) * u j)) * thr P / P.N i := by
      push_cast; field_simp
    rw [e1, h1]; field_simp
  have hL : (∑ i, (starRingEnd ℂ) (u i) * ∑ j, (Kmat P x i j : ℂ) * u j) =
      (z * thr P) * ((∑ i, ((u i).re ^ 2 + (u i).im ^ 2) / P.N i : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [heig i]
    have hc : (starRingEnd ℂ) (u i) * u i = (((u i).re ^ 2 + (u i).im ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_apply]; push_cast; ring
    push_cast at hc
    calc (starRingEnd ℂ) (u i) * (z * (thr P : ℂ) * (u i / (P.N i : ℂ)))
        = z * thr P * (((starRingEnd ℂ) (u i) * u i) / P.N i) := by ring
      _ = _ := by rw [hc]
  have hQ := quad_split (Kmat P x) (K_symm P x) u
  rw [hL] at hQ
  set a : Fin n → ℝ := fun i => (u i).re
  set b : Fin n → ℝ := fun i => (u i).im
  set dR : ℝ := ∑ i, ((u i).re ^ 2 + (u i).im ^ 2) / P.N i
  set kR : ℝ := a ⬝ᵥ (Kmat P x *ᵥ a) + b ⬝ᵥ (Kmat P x *ᵥ b)
  have hpsd := K_psd P hP x hx
  have hka : 0 ≤ a ⬝ᵥ (Kmat P x *ᵥ a) := by simpa using hpsd.dotProduct_mulVec_nonneg a
  have hkb : 0 ≤ b ⬝ᵥ (Kmat P x *ᵥ b) := by simpa using hpsd.dotProduct_mulVec_nonneg b
  have hAnn : ∀ y : Fin n → ℝ, 0 ≤ y ⬝ᵥ ((thr P • (Nhat P)⁻¹ - Kmat P x) *ᵥ y) := fun y => by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg y
  have hApos : ∀ y : Fin n → ℝ, y ≠ 0 → 0 < y ⬝ᵥ ((thr P • (Nhat P)⁻¹ - Kmat P x) *ᵥ y) :=
    fun y hy => by simpa using hA.dotProduct_mulVec_pos hy
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h; push Not at h
    apply hu0; funext i
    apply Complex.ext
    · simpa [a] using congrFun h.1 i
    · simpa [b] using congrFun h.2 i
  have hsum : 0 < a ⬝ᵥ ((thr P • (Nhat P)⁻¹ - Kmat P x) *ᵥ a) +
      b ⬝ᵥ ((thr P • (Nhat P)⁻¹ - Kmat P x) *ᵥ b) := by
    rcases hab with h | h
    · exact add_pos_of_pos_of_nonneg (hApos a h) (hAnn b)
    · exact add_pos_of_nonneg_of_pos (hAnn a) (hApos b h)
  rw [qA_eq P hP x a, qA_eq P hP x b] at hsum
  have hdR : dR = ∑ i, a i ^ 2 / P.N i + ∑ i, b i ^ 2 / P.N i := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  have hlt : kR < thr P * dR := by rw [hdR]; nlinarith
  have hdpos : 0 < dR := by
    by_contra h; push Not at h
    nlinarith
  have hz' : z = ((kR / (thr P * dR) : ℝ) : ℂ) := by
    have hd : (dR : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
    push_cast
    rw [eq_div_iff (mul_ne_zero hT hd)]
    rw [← hQ]; ring
  rw [hz', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_lt_one (by positivity)]
  exact hlt

lemma forward (P : Params n) (hP : P.Standing) (x : Fin n → ℝ) (hx : IsActivity x)
    (hA : ¬ (thr P • (Nhat P)⁻¹ - Kmat P x).PosDef) :
    ∃ z ∈ spectrum ℂ ((Fmat P x * Vinv P).map (algebraMap ℝ ℂ)), 1 ≤ ‖z‖ := by
  have hthr := thr_pos P hP
  have hN := hP.1
  set Ns := Nsqrt P with hNs
  have hNsT : star Ns = Ns := by
    simp [hNs, Nsqrt, star_eq_conjTranspose, diagonal_conjTranspose]
  have hNsH : Nsᴴ = Ns := by rw [← star_eq_conjTranspose]; exact hNsT
  have hNsU : IsUnit Ns := by
    rw [isUnit_iff_isUnit_det, hNs, Nsqrt, det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (Real.sqrt_pos.2 (hN i)).ne'
  have hD : Ns * diagonal (fun i => 1 / P.N i) * Ns = 1 := by
    rw [hNs, Nsqrt, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    have h := hN i
    have h2 := Real.mul_self_sqrt h.le
    calc Real.sqrt (P.N i) * (1 / P.N i) * Real.sqrt (P.N i)
        = (Real.sqrt (P.N i) * Real.sqrt (P.N i)) / P.N i := by ring
      _ = 1 := by rw [h2, div_self h.ne']
  have hH : Ns * (thr P • (Nhat P)⁻¹ - Kmat P x) * Ns = thr P • 1 - Ns * Kmat P x * Ns := by
    rw [Dinv P hP, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hD]
  have hnot : ¬ (thr P • 1 - Ns * Kmat P x * Ns).PosDef := by
    rw [← hH]; intro h; apply hA
    have := hNsU.posDef_star_left_conjugate_iff (x := thr P • (Nhat P)⁻¹ - Kmat P x)
    rw [hNsT] at this
    exact this.1 h
  have hKH : (Kmat P x)ᴴ = Kmat P x := (K_psd P hP x hx).1
  have hHerm : (thr P • 1 - Ns * Kmat P x * Ns).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, conjTranspose_mul,
      conjTranspose_mul, hNsH, hKH, star_trivial, Matrix.mul_assoc]
  rw [hHerm.posDef_iff_eigenvalues_pos] at hnot
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  set lam := hHerm.eigenvalues i with hlam
  have he := hHerm.mulVec_eigenvectorBasis i
  set e : Fin n → ℝ := ⇑(hHerm.eigenvectorBasis i) with he_def
  have he0 : e ≠ 0 := by
    intro h0
    have h1 := (hHerm.eigenvectorBasis).orthonormal.1 i
    have h3 : hHerm.eigenvectorBasis i = 0 := by
      ext j; simpa [e] using congrFun h0 j
    rw [h3, norm_zero] at h1
    exact zero_ne_one h1
  have hS : (Ns * Kmat P x * Ns) *ᵥ e = (thr P - lam) • e := by
    have h := he
    rw [sub_mulVec, smul_mulVec, one_mulVec] at h
    rw [sub_smul, ← h, sub_sub_cancel]
  set u : Fin n → ℝ := Ns *ᵥ e with hu
  have hu0 : u ≠ 0 := by
    intro h; apply he0
    exact mulVec_injective_of_isUnit hNsU (h.trans (mulVec_zero Ns).symm)
  have hNN : Ns * Ns = Nhat P := by
    rw [hNs, Nsqrt, Nhat, diagonal_mul_diagonal]; congr 1; funext j
    exact Real.mul_self_sqrt (hN j).le
  have hFb : Fbar P x = Nhat P * Kmat P x := by
    ext j k; rw [Fbar_eq, Nhat, diagonal_mul]
  have hFu' : Fbar P x *ᵥ u = (thr P - lam) • u := by
    rw [hFb, ← hNN, hu]
    calc (Ns * Ns * Kmat P x) *ᵥ (Ns *ᵥ e) = Ns *ᵥ ((Ns * Kmat P x * Ns) *ᵥ e) := by
          rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = (thr P - lam) • (Ns *ᵥ e) := by rw [hS, mulVec_smul]
  have hFu : ∀ j, ∑ k, Fbar P x j k * u k = (thr P - lam) * u j := by
    intro j; have := congrFun hFu' j; simpa [mulVec, dotProduct] using this
  refine ⟨((1 / thr P * (thr P - lam) : ℝ) : ℂ), ?_, ?_⟩
  · rw [mem_spec]
    refine ⟨extv (fun j => (u j : ℂ)), ?_, ?_⟩
    · intro h; apply hu0; funext j
      have := congrFun h (0, j)
      simp only [extv, Pi.zero_apply] at this
      rw [if_pos trivial] at this
      exact_mod_cast this
    · funext p; rw [Mc_ext P hP x]; rcases p with ⟨p1, j⟩
      by_cases h : p1 = 0
      · subst h
        simp only [extv, Pi.smul_apply, smul_eq_mul]
        rw [if_pos trivial, if_pos trivial]
        have : ∑ k, (Fbar P x j k : ℂ) * (u k : ℂ) = (((thr P - lam) * u j : ℝ) : ℂ) := by
          rw [← hFu j]; push_cast; rfl
        rw [this]; push_cast; ring
      · simp [extv, h]
  · rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 : 1 / thr P * (thr P - lam) = 1 + (-lam) / thr P := by field_simp; ring
    have h2 : 0 ≤ (-lam) / thr P := div_nonneg (by linarith) hthr.le
    have h3 : 1 ≤ 1 / thr P * (thr P - lam) := by rw [h1]; linarith
    exact h3.trans (le_abs_self _)

end TCS23664385

open TargetedClosure.Stability in
theorem solution {n : ℕ} (P : Params n) (hP : P.Standing)
    (x : Fin n → ℝ) (hx : IsActivity x) :
    Re P x < 1 ↔
    (thr P • (Nhat P)⁻¹ - Tmat P * Xmat x * Lam P * (Tmat P).transpose).PosDef := by
  have hA_eq : (thr P • (Nhat P)⁻¹ - Tmat P * Xmat x * Lam P * (Tmat P).transpose) =
      thr P • (Nhat P)⁻¹ - TCS23664385.Kmat P x := rfl
  rw [hA_eq]
  have hRe : Re P x = spectralRadius ℂ ((Fmat P x * Vinv P).map (algebraMap ℝ ℂ)) := by
    rw [Re, lam1, TCS23664385.Vinv_eq P hP]
  rw [hRe]
  constructor
  · intro h
    by_contra hA
    obtain ⟨z, hz, hz1⟩ := TCS23664385.forward P hP x hx hA
    have : (1 : ENNReal) ≤ spectralRadius ℂ ((Fmat P x * Vinv P).map (algebraMap ℝ ℂ)) := by
      refine le_trans ?_ (le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ
        ((Fmat P x * Vinv P).map (algebraMap ℝ ℂ))) => (‖k‖₊ : ENNReal)) z hz)
      have : (1 : NNReal) ≤ ‖z‖₊ := by
        rw [← NNReal.coe_le_coe, coe_nnnorm]; simpa using hz1
      exact_mod_cast this
    exact absurd h (not_lt.2 this)
  · intro hA
    exact TCS23664385.sup_lt _ (Matrix.finite_spectrum _)
      (fun z hz => TCS23664385.backward P hP x hx hA z hz)
