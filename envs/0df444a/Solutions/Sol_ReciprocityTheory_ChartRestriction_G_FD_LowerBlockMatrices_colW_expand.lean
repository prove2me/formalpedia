-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices.colW_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:56:06.937224+00:00
-- url     : https://prove2.me/submissions/62ec3504-f65f-4740-9f34-d2971d19f75f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BlockIdentityExpansion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowerBlockMatrices
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LowerBlockMatrices_mulVec_eq_sum_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mulVec_eq_sum_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_sum_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma hermC_sum_smul_left' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {m : ℕ}
    (c : Fin m → ℂ) (y : Fin m → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ b, c b • y b) v = ∑ b, c b * hermC τ G (y b) v := by
  simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b' _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring
end
end ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
theorem _root_.solution (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 : Frame X.Ψ r) {x0 : Frame X.Ψ r}
    (hortho : X.IsOrtho x0) (τ : X.Ψ) (hdet0 : (mat x0 τ).det ≠ 0) (b : Fin X.p0) :
    col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) =
      ∑ b', Amat X h1 z0 x0 τ b' b • col (mat x0 τ) (Fin.castLE X.p0_le b') +
        ∑ a, Bmat X h1 z0 x0 τ a b • col (mat x0 τ) (kap X.p0_le a) := by
  classical
  set y := col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) with hy
  set α := (mat x0 τ)⁻¹ *ᵥ y with hα
  have hyα : y = ∑ c, α c • col (mat x0 τ) c := by
    rw [← mulVec_eq_sum_col, hα, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet0), Matrix.one_mulVec]
  have hcd : ∀ c d, hermC τ.1 X.Gm (col (mat x0 τ) c) (col (mat x0 τ) d) =
      if c = d then ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) else 0 := by
    intro c d
    have := congrFun (congrFun (hortho τ) c) d
    simpa [gram, Matrix.diagonal_apply] using this
  have hh : ∀ d, hermC τ.1 X.Gm y (col (mat x0 τ) d) = α d * ((sgn X.p0 (d : ℕ) : ℝ) : ℂ) := by
    intro d
    rw [hyα, hermC_sum_smul_left']
    simp only [hcd, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  rw [hyα, sum_split X.p0_le]
  congr 1
  · refine Finset.sum_congr rfl fun b' _ ↦ ?_
    congr 1
    simp only [Amat, Matrix.of_apply]
    rw [← hy, hh]
    have hb' := b'.isLt
    simp [sgn, hb']
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    congr 1
    simp only [Bmat, Matrix.of_apply]
    rw [← hy, hh, show sgn X.p0 (kap X.p0_le a : ℕ) = -1 by simp [sgn, kap]]
    push_cast
    ring
end ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
