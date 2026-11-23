-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.comb_orth_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:44.689037+00:00
-- url     : https://prove2.me/submissions/f87c80b9-732e-42a1-805c-e9465cec7514

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_sum_left

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
variable {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ)
namespace ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
theorem _root_.solution {n : ℕ} (f : Fin n → Fin r → ℂ) (hA : IsUnit (gramF τ G f).det)
    (w : Fin n → ℂ) (h : ∀ d, hermC τ G (∑ b, w b • f b) (f d) = 0) : ∑ b, w b • f b = 0 := by
  have hv : Matrix.vecMul w (gramF τ G f) = 0 := by
    funext d
    have hd := h d
    rw [hC_sum_left] at hd
    simpa [Matrix.vecMul, dotProduct, gramF] using hd
  have hw : w = 0 := by
    have h2 := congrArg (fun x => Matrix.vecMul x (gramF τ G f)⁻¹) hv
    simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hA] using h2
  simp [hw]
end ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
