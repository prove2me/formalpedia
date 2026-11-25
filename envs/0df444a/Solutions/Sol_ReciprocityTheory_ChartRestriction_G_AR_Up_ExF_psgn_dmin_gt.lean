-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.psgn_dmin_gt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:35.700102+00:00
-- url     : https://prove2.me/submissions/41b7b955-e9a2-4f97-abbb-273e092ca98a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_neg_of_perp__512163f6e248
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_psgn_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
theorem _root_.solution {x : Frame X.Ψ r} (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0)
    (hA : (X.gramPos x τ).PosDef) (k : ℕ) (hk : X.p0 + k ≤ r) (i : Fin (r + 1))
    (hik : (i : ℕ) = X.p0 + k) : 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
  classical
  have hG := X.Gm_herm
  let gr : Fin k → Fin r := fun j => ⟨X.p0 + j, by have := j.isLt; omega⟩
  let d : Fin k → Fin r → ℂ := fun j => FD.col (mat x τ) (gr j)
  let A : Matrix (Fin X.p0) (Fin X.p0) ℂ := X.gramPos x τ
  let B : Matrix (Fin X.p0) (Fin k) ℂ := fun a l => hermC τ.1 X.Gm (X.colP x τ a) (d l)
  let C : Matrix (Fin k) (Fin X.p0) ℂ := fun j b => hermC τ.1 X.Gm (d j) (X.colP x τ b)
  let D : Matrix (Fin k) (Fin k) ℂ := fun j l => hermC τ.1 X.Gm (d j) (d l)
  have hApos : 0 < A.det := Matrix.PosDef.det_pos hA
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hApos.ne'
  haveI : Invertible A := Matrix.invertibleOfIsUnitDet A hAu
  have hdm : dmin X.Gm x τ i = (Matrix.fromBlocks A B C D).det := by
    let e : Fin X.p0 ⊕ Fin k ≃ Fin (i : ℕ) := finSumFinEquiv.trans (finCongr hik.symm)
    unfold dmin lminor
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext s t
    rcases s with a | j <;> rcases t with b | l <;> rfl
  rw [hdm, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  set α : Matrix (Fin k) (Fin X.p0) ℂ := C * A⁻¹ with hαdef
  have hαA : α * A = C := by
    rw [hαdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]
  have hAab : ∀ a b, A a b = hermC τ.1 X.Gm (X.colP x τ a) (X.colP x τ b) := fun a b => by
    show X.gramPos x τ a b = _
    rw [Data.gramPos_apply]
  let wv : Fin k → Fin r → ℂ := fun j => d j + ∑ a, (-α j a) • X.colP x τ a
  have hwc : ∀ j b, hermC τ.1 X.Gm (wv j) (X.colP x τ b) = 0 := by
    intro j b
    show hermC τ.1 X.Gm (d j + ∑ a, (-α j a) • X.colP x τ a) (X.colP x τ b) = 0
    rw [hermC_add_left, hermC_sum_left]
    simp only [hermC_smul_left]
    have h1 : ∑ a, -α j a * hermC τ.1 X.Gm (X.colP x τ a) (X.colP x τ b) = -(α * A) j b := by
      rw [Matrix.mul_apply, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hAab]
      ring
    rw [h1, hαA]
    exact add_neg_cancel _
  have hSw : ∀ j l, (D - α * B) j l = hermC τ.1 X.Gm (wv j) (wv l) := by
    intro j l
    have h2 : hermC τ.1 X.Gm (wv j) (wv l) = hermC τ.1 X.Gm (wv j) (d l) := by
      show hermC τ.1 X.Gm (wv j) (d l + ∑ a, (-α l a) • X.colP x τ a) = _
      rw [hermC_add_right, hermC_sum_right]
      simp only [hermC_smul_right, hwc, mul_zero, Finset.sum_const_zero, add_zero]
    have h3 : hermC τ.1 X.Gm (wv j) (d l) = D j l - (α * B) j l := by
      show hermC τ.1 X.Gm (d j + ∑ a, (-α j a) • X.colP x τ a) (d l) = _
      rw [hermC_add_left, hermC_sum_left, Matrix.mul_apply, sub_eq_add_neg,
        ← Finset.sum_neg_distrib]
      simp only [hermC_smul_left]
      congr 1
      exact Finset.sum_congr rfl fun a _ => neg_mul _ _
    rw [Matrix.sub_apply, h2, h3]
  have hSH : (D - α * B).IsHermitian := Matrix.IsHermitian.ext fun j l => by
    rw [hSw, hSw]
    exact hermC_conj τ.1 hG _ _
  have hli0 : LinearIndependent ℂ (fun m => FD.col (mat x τ) m) :=
    Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hg : Function.Injective (Sum.elim (Fin.castLE X.p0_le) gr) := by
    intro s t hst
    rcases s with a | j <;> rcases t with b | l
    · exact congrArg Sum.inl (Fin.castLE_injective X.p0_le hst)
    · exfalso
      have h1 := congrArg Fin.val hst
      have := a.isLt
      simp only [Sum.elim_inl, Sum.elim_inr, gr, Fin.coe_castLE, Fin.val_mk] at h1
      omega
    · exfalso
      have h1 := congrArg Fin.val hst
      have := b.isLt
      simp only [Sum.elim_inl, Sum.elim_inr, gr, Fin.coe_castLE, Fin.val_mk] at h1
      omega
    · have h1 := congrArg Fin.val hst
      simp only [Sum.elim_inl, Sum.elim_inr, gr, Fin.coe_castLE, Fin.val_mk] at h1
      exact congrArg Sum.inr (Fin.ext (by omega))
  have hli := hli0.comp _ hg
  have hS : (-(D - α * B)).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hSH.neg fun xv hxv => ?_
    set W : Fin r → ℂ := ∑ j, conj (xv j) • wv j with hWdef
    have hq : star xv ⬝ᵥ ((-(D - α * B)) *ᵥ xv) = -hermC τ.1 X.Gm W W := by
      rw [hWdef, hermC_sum_left]
      simp only [hermC_smul_left, hermC_sum_right, hermC_smul_right, Complex.conj_conj,
        dotProduct, Matrix.mulVec, Matrix.neg_apply, hSw, Pi.star_apply, Finset.mul_sum]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Complex.star_def]
      ring
    have hWc : ∀ b, hermC τ.1 X.Gm W (X.colP x τ b) = 0 := by
      intro b
      rw [hWdef, hermC_sum_left]
      exact Finset.sum_eq_zero fun j _ => by rw [hermC_smul_left, hwc j b, mul_zero]
    have hW0 : W ≠ 0 := by
      intro hW
      let coef : Fin X.p0 ⊕ Fin k → ℂ :=
        Sum.elim (fun a => ∑ j, conj (xv j) * -α j a) (fun j => conj (xv j))
      have hsum : ∑ s, coef s • FD.col (mat x τ) (Sum.elim (Fin.castLE X.p0_le) gr s) = W := by
        rw [Fintype.sum_sum_type, hWdef]
        simp only [coef, Sum.elim_inl, Sum.elim_inr, wv, d, smul_add, Finset.sum_add_distrib,
          Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [add_comm, Finset.sum_comm]
        rfl
      have h0 : ∑ s, coef s • ((fun m => FD.col (mat x τ) m) ∘ Sum.elim (Fin.castLE X.p0_le) gr) s
          = 0 := hsum.trans hW
      have hcoef := Fintype.linearIndependent_iff.1 hli coef h0
      apply hxv
      funext j
      have := hcoef (Sum.inr j)
      simpa [coef] using this
    have hneg := neg_of_perp' X τ hA hW0 hWc
    have him : (hermC τ.1 X.Gm W W).im = 0 :=
      Complex.conj_eq_iff_im.1 (hermC_conj τ.1 hG W W)
    rw [hq, Complex.lt_def]
    constructor
    · simp only [Complex.zero_re, Complex.neg_re]
      linarith
    · simp [him]
  have hSpos : 0 < (-(D - α * B)).det := Matrix.PosDef.det_pos hS
  have hdetS : (D - α * B).det = (-1) ^ k * (-(D - α * B)).det := by
    rw [Matrix.det_neg, Fintype.card_fin, ← mul_assoc, ← mul_pow]
    norm_num
  rw [hdetS, hik, OrthonormalChartBounds.psgn_add]
  have hz : A.det * ((-1) ^ k * (-(D - α * B)).det) =
      (((-1 : ℝ) ^ k : ℝ) : ℂ) * (A.det * (-(D - α * B)).det) := by
    push_cast
    ring
  have hre : 0 < (A.det * (-(D - α * B)).det).re := by
    have := (Complex.lt_def.1 (mul_pos hApos hSpos)).1
    simpa using this
  have h1 : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hz, Complex.re_ofReal_mul, ← mul_assoc, h1, one_mul]
  exact hre
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
