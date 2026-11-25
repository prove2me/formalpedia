-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.exists_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:54:29.295699+00:00
-- url     : https://prove2.me/submissions/06dbbc29-45a9-435a-b799-7b69b5268a33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantNormalForms_col_mul_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantNormalForms_Hf_sum_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantNormalForms_hgram_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms
open Matrix NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    ∃ B : Matrix (Fin r) (Fin r) ℂ, B.det ≠ 0 ∧ (∀ a c : Fin r, c < a → B a c = 0) ∧
      ∀ a c : Fin r, X.Hf x τ (col (mat x τ * B) a) (col (mat x τ * B) c) =
        if a = c then 1 else 0 := by
  have hH := hgram_posDef X hx τ
  obtain ⟨H, hHd⟩ : ∃ H : Matrix (Fin r) (Fin r) ℂ,
      H = Matrix.of fun a c => X.Hf x τ (col (mat x τ) a) (col (mat x τ) c) := ⟨_, rfl⟩
  rw [← hHd] at hH
  have hD := LDL.diag_eq_lowerInv_conj hH
  have hLdet : (LDL.lowerInv hH).det ≠ 0 := (Matrix.isUnit_det_of_invertible _).ne_zero
  obtain ⟨D, hDd⟩ : ∃ D : Matrix (Fin r) (Fin r) ℂ,
      D = LDL.lowerInv hH * H * (LDL.lowerInv hH)ᴴ := ⟨_, rfl⟩
  have hDoff : ∀ a c, a ≠ c → D a c = 0 := by
    intro a c hac
    rw [hDd, ← hD]
    exact Matrix.diagonal_apply_ne _ hac
  have hdpos : ∀ i : Fin r, 0 < (D i i).re ∧ (D i i).im = 0 := by
    intro i
    have hx0 : star (LDL.lowerInv hH i) ≠ 0 := by
      intro h0
      apply hLdet
      apply Matrix.det_eq_zero_of_row_eq_zero i
      intro j
      have h1 := congrFun h0 j
      simpa using h1
    have hp := hH.dotProduct_mulVec_pos hx0
    have he : D i i = star (star (LDL.lowerInv hH i)) ⬝ᵥ (H *ᵥ star (LDL.lowerInv hH i)) := by
      rw [hDd]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec,
        star_star, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    rw [he]
    exact ⟨(Complex.lt_def.mp hp).1, (Complex.lt_def.mp hp).2.symm⟩
  obtain ⟨s, hs⟩ : ∃ s : Fin r → ℝ, s = fun c => (Real.sqrt (D c c).re)⁻¹ := ⟨_, rfl⟩
  have hs0 : ∀ c, s c ≠ 0 := fun c => by
    rw [hs]
    exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (hdpos c).1)
  refine ⟨(LDL.lowerInv hH)ᵀ * diagonal (fun c => (s c : ℂ)), ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    exact mul_ne_zero hLdet (Finset.prod_ne_zero_iff.mpr fun c _ =>
      Complex.ofReal_ne_zero.mpr (hs0 c))
  · intro a c hca
    rw [Matrix.mul_diagonal, Matrix.transpose_apply, LDL.lowerInv_triangular hH hca, zero_mul]
  · intro a c
    rw [col_mul_eq, col_mul_eq, Hf_sum_sum]
    have hHkl : ∀ k l, X.Hf x τ (col (mat x τ) k) (col (mat x τ) l) = H k l := fun k l => by
      rw [hHd]
      rfl
    simp only [hHkl, Matrix.mul_diagonal, Matrix.transpose_apply]
    calc _ = (s a : ℂ) * (s c : ℂ) * D a c := by
          rw [hDd]
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, map_mul,
            Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
          conv_rhs => rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
      _ = if a = c then 1 else 0 := by
          by_cases hac : a = c
          · subst hac
            rw [if_pos rfl]
            have hr := (hdpos a).1
            have hre : D a a = ((D a a).re : ℂ) := Complex.ext rfl (by simp [(hdpos a).2])
            have hsq : Real.sqrt (D a a).re * Real.sqrt (D a a).re = (D a a).re :=
              Real.mul_self_sqrt hr.le
            have hne : Real.sqrt (D a a).re ≠ 0 := Real.sqrt_ne_zero'.mpr hr
            have h1 : s a * s a * (D a a).re = 1 := by
              rw [hs, ← hsq]
              field_simp
            rw [hre]
            exact_mod_cast h1
          · rw [if_neg hac, hDoff a c hac, mul_zero]
end ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms
