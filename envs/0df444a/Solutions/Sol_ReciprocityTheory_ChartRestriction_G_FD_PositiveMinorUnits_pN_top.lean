-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.pN_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:59.56307+00:00
-- url     : https://prove2.me/submissions/079e6ed2-fb69-4854-8f05-a48b760e23eb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_unit_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_comb_orth_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_pv_orth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
variable {τ G} (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (p0 : ℕ) (hp0 : p0 ≤ r)
  (x : Matrix (Fin r) (Fin r) ℂ) (hx : x.det ≠ 0)
  (hsg : ∀ i (h : i ≤ r), 0 < psgn p0 i * (gramF τ G (famN x i h)).det.re)
  (e : Fin r → ℂ) (he : hermC τ G e e = 0)
include hsg
include hG
include hx
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
theorem _root_.solution : pN τ G x e r = e := by
  have hA := unit_of p0 x hsg r le_rfl
  rw [pN, dif_pos le_rfl]
  have he' : e = ∑ d, (x⁻¹ *ᵥ e) d • famN x r le_rfl d := by
    have h1 : x *ᵥ (x⁻¹ *ᵥ e) = e := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hx),
        Matrix.one_mulVec]
    conv_lhs => rw [← h1]
    funext k
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, famN, col]
    exact Finset.sum_congr rfl fun d _ => by rw [mul_comm]; rfl
  have h2 : e - pv τ G (famN x r le_rfl) e = ∑ d, ((x⁻¹ *ᵥ e) d - yv τ G (famN x r le_rfl) e d) •
      famN x r le_rfl d := by
    conv_lhs => arg 1; rw [he']
    rw [pv, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => (sub_smul _ _ _).symm
  have h3 := comb_orth_zero τ G (famN x r le_rfl) hA _ fun d => by
    rw [← h2, hC_sub_left, pv_orth τ G _ e hA d]; exact sub_self _
  rw [← h2] at h3
  exact (sub_eq_zero.mp h3).symm
end ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
