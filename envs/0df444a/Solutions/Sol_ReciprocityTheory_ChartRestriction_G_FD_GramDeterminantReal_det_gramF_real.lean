-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.det_gramF_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:44.648132+00:00
-- url     : https://prove2.me/submissions/3b474741-7e9c-44d7-8800-e255f802feef

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
variable {τ G} (hG : ∀ a b, τ (G b a) = conj (τ (G a b)))
include hG
namespace ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
theorem _root_.solution {n : ℕ} (f : Fin n → Fin r → ℂ) : (gramF τ G f).det.im = 0 := by
  have h : (gramF τ G f)ᴴ = gramF τ G f := by
    ext a b
    rw [Matrix.conjTranspose_apply]
    simp only [gramF, Matrix.of_apply]
    rw [hC_conj hG (f b) (f a), starRingEnd_apply]
  have h2 := Matrix.det_conjTranspose (gramF τ G f)
  rw [h] at h2
  apply Complex.conj_eq_iff_im.mp
  rw [starRingEnd_apply]
  exact h2.symm
end ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
