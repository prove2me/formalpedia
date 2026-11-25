-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_neg_of_perp__512163f6e248
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:18.933595+00:00
-- url     : https://prove2.me/submissions/3b306bb0-1785-445d-895b-5868fa7c35e3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_quad_re_pos


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
theorem _root_.solution {x : Frame X.Ψ r} (τ : X.Ψ) (hA : (X.gramPos x τ).PosDef) {e : Fin r → ℂ}
    (he : e ≠ 0) (hperp : ∀ b, hermC τ.1 X.Gm e (X.colP x τ b) = 0) :
    (hermC τ.1 X.Gm e e).re < 0 := by
  classical
  obtain ⟨P, hPdet, hPgram⟩ := X.signature τ
  have hG := X.Gm_herm
  have hg : ∀ a b, hermC τ.1 X.Gm (FD.col P a) (FD.col P b) =
      Matrix.diagonal (fun a : Fin r => ((sgn X.p0 a : ℝ) : ℂ)) a b := fun a b => by
    rw [← hPgram]; rfl
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hPdet
  have hcoord : ∀ u : Fin r → ℂ, ∑ a, (P⁻¹ *ᵥ u) a • FD.col P a = u := by
    intro u
    have h1 : P *ᵥ (P⁻¹ *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]
    conv_rhs => rw [← h1]
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FD.col, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hquad : ∀ y : Fin r → ℂ, hermC τ.1 X.Gm (∑ a, y a • FD.col P a) (∑ b, y b • FD.col P b) =
      ∑ a, y a * conj (y a) * ((sgn X.p0 a : ℝ) : ℂ) := by
    intro y
    rw [hermC_sum_left]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hermC_smul_left, hermC_sum_right]
    simp_rw [hermC_smul_right, hg, Matrix.diagonal_apply]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  by_contra hcon
  push_neg at hcon
  let Q : Matrix (Fin r) (Option (Fin X.p0)) ℂ :=
    fun k o => Option.elim o (e k) (fun b => X.colP x τ b k)
  let R : Matrix (Fin X.p0) (Option (Fin X.p0)) ℂ := (P⁻¹ * Q).submatrix (Fin.castLE X.p0_le) id
  have hker : LinearMap.ker (Matrix.mulVecLin R) ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hz
  have hQv : Q *ᵥ z = ∑ b, z (some b) • X.colP x τ b + z none • e := by
    funext k
    simp only [Q, Matrix.mulVec, dotProduct, Fintype.sum_option, Option.elim, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    · exact mul_comm _ _
  have hy0 : ∀ a : Fin X.p0,
      (P⁻¹ *ᵥ (∑ b, z (some b) • X.colP x τ b + z none • e)) (Fin.castLE X.p0_le a) = 0 := by
    intro a
    have h3 : ((P⁻¹ * Q) *ᵥ z) (Fin.castLE X.p0_le a) = 0 := congrFun hz a
    rwa [← Matrix.mulVec_mulVec, hQv] at h3
  set w : Fin r → ℂ := ∑ b, z (some b) • X.colP x τ b with hwdef
  set v : Fin r → ℂ := w + z none • e with hvdef
  set y : Fin r → ℂ := P⁻¹ *ᵥ v with hydef
  have hvP : v = ∑ k, y k • FD.col P k := (hcoord v).symm
  have hsg : ∀ k, y k * conj (y k) * ((sgn X.p0 k : ℝ) : ℂ) =
      -((Complex.normSq (y k) : ℝ) : ℂ) := by
    intro k
    by_cases hk : (k : ℕ) < X.p0
    · have : y k = 0 := hy0 ⟨k, hk⟩
      simp [this]
    · simp [sgn, hk, Complex.mul_conj]
  have hvv1 : hermC τ.1 X.Gm v v = -∑ k, ((Complex.normSq (y k) : ℝ) : ℂ) := by
    rw [hvP, hquad]
    simp only [hsg, Finset.sum_neg_distrib]
  have hwe : hermC τ.1 X.Gm w e = 0 := by
    rw [hwdef, hermC_sum_left]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [hermC_smul_left, ← hermC_conj τ.1 hG, hperp b, map_zero, mul_zero]
  have hew : hermC τ.1 X.Gm e w = 0 := by
    rw [hwdef, hermC_sum_right]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [hermC_smul_right, hperp b, mul_zero]
  have hvv2 : hermC τ.1 X.Gm v v =
      hermC τ.1 X.Gm w w + z none * conj (z none) * hermC τ.1 X.Gm e e := by
    rw [hvdef]
    simp only [hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right, hwe, hew]
    ring
  have hwq : hermC τ.1 X.Gm w w =
      ∑ a, ∑ b, z (some a) * X.gramPos x τ a b * conj (z (some b)) := by
    rw [hwdef, hermC_sum_left]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hermC_smul_left, hermC_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hermC_smul_right, Data.gramPos_apply]
    ring
  have hre : (hermC τ.1 X.Gm v v).re =
      (hermC τ.1 X.Gm w w).re + Complex.normSq (z none) * (hermC τ.1 X.Gm e e).re := by
    rw [hvv2, Complex.mul_conj, Complex.add_re, Complex.re_ofReal_mul]
  have hre2 : (hermC τ.1 X.Gm v v).re = -∑ k, Complex.normSq (y k) := by
    rw [hvv1]; simp
  have hww : 0 ≤ (hermC τ.1 X.Gm w w).re := by
    by_cases hz1 : (fun b => z (some b)) = 0
    · have hw0 : w = 0 := by
        rw [hwdef]
        simp [show ∀ b, z (some b) = 0 from fun b => congrFun hz1 b]
      rw [hw0]; simp [hermC]
    · rw [hwq]; exact (quad_re_pos hA hz1).le
  have hnn : 0 ≤ (hermC τ.1 X.Gm v v).re := by
    rw [hre]; exact add_nonneg hww (mul_nonneg (Complex.normSq_nonneg _) hcon)
  have hy : ∀ k, y k = 0 := by
    have hs : ∑ k, Complex.normSq (y k) = 0 := by
      have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => Complex.normSq_nonneg (y k))
      rw [hre2] at hnn
      linarith
    intro k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg (y k))).1 hs k
      (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 this
  have hv0 : v = 0 := by
    rw [hvP]; simp [hy]
  have hzs : (fun b => z (some b)) = 0 := by
    by_contra hz1
    have h1 := quad_re_pos hA hz1
    rw [← hwq] at h1
    have h0 : (hermC τ.1 X.Gm v v).re = 0 := by rw [hv0]; simp [hermC]
    rw [hre] at h0
    nlinarith [mul_nonneg (Complex.normSq_nonneg (z none)) hcon]
  have hw0 : w = 0 := by
    rw [hwdef]
    simp [show ∀ b, z (some b) = 0 from fun b => congrFun hzs b]
  have ht0 : z none = 0 := by
    have h := hv0
    rw [hvdef, hw0, zero_add] at h
    exact (smul_eq_zero.1 h).resolve_right he
  apply hz0
  funext o
  cases o with
  | none => exact ht0
  | some b => exact congrFun hzs b
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
