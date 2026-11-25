-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:29:31.370481+00:00
-- url     : https://prove2.me/submissions/4ec57051-d1ce-4d84-b71d-8dbeb17ad1a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_sgn_mul_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_ortho_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_sgn_mul_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
theorem _root_.solution {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0) (y : Fin r → ℂ) :
    y = ∑ c : Fin r, (((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * hermC τ.1 X.Gm y (col (mat x τ) c)) • col (mat x τ) c := by
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr hdet
  obtain ⟨t, ht⟩ : ∃ t : Fin r → ℂ, y = ∑ c, t c • col (mat x τ) c := by
    refine ⟨(mat x τ)⁻¹ *ᵥ y, ?_⟩
    have h1 : mat x τ *ᵥ ((mat x τ)⁻¹ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    conv_lhs => rw [← h1]
    funext k
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col]
    exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
  have hc : ∀ c, hermC τ.1 X.Gm y (col (mat x τ) c) = t c * ((sgn X.p0 c : ℝ) : ℂ) := by
    intro c
    rw [ht, hermC_sum_left]
    simp_rw [hermC_smul_left, ortho_apply X hx τ]
    simp
  conv_lhs => rw [ht]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [hc c, mul_comm (t c), ← mul_assoc, sgn_mul_self, one_mul]
end ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
