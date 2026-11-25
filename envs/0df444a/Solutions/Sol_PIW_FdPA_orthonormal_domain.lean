-- Prove2me | solution 1 for PIW.FdPA.orthonormal_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:42:01.719174+00:00
-- url     : https://prove2.me/submissions/daf3573a-4e2d-4dba-bdfc-797a15ef20a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Theorems.Thm_PIW_FdPA_mem_dom_iff
import Theorems.Thm_PIW_FdPA_det_of_minors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
open scoped ComplexConjugate
noncomputable section
namespace PIW.FdPA
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] : OrthoDom E := by
  intro r X x hx
  rw [mem_dom_iff]
  intro τ
  have hdm : ∀ i : Fin (r + 1), dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    intro i
    simp only [dmin, lminor, hx τ]
    rw [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    simp [psgn, Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ))]
  have hps : ∀ i : ℕ, psgn X.p0 i ≠ 0 := by
    intro i
    unfold psgn
    refine Finset.prod_ne_zero_iff.mpr (fun a _ => ?_)
    unfold sgn
    split_ifs <;> norm_num
  have hpos : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
    intro i
    rw [hdm, Complex.ofReal_re]
    exact mul_self_pos.mpr (hps i)
  exact ⟨det_of_minors X x τ hpos, hpos⟩
end PIW.FdPA
