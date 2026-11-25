-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary.perp_span_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:13.285585+00:00
-- url     : https://prove2.me/submissions/18728e82-5936-45f7-8f5f-193b5c95428f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpSpanRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
namespace ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
theorem _root_.solution (hG : ∀ a b, cc (G a b) = G b a) {s : Set (Fin r → ℂ)} {v : Fin r → ℂ}
    (h : ∀ y ∈ s, hermC τ G v y = 0) : ∀ y ∈ Submodule.span ℂ s, hermC τ G v y = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp [hermC]
  | add x y _ _ hx hy =>
    have e : hermC τ G v (x + y) = hermC τ G v x + hermC τ G v y := by
      simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
    rw [e, hx, hy, add_zero]
  | smul c x _ hx =>
    have e : hermC τ G v (c • x) = conj c * hermC τ G v x := by
      simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      ring
    rw [e, hx, mul_zero]
end ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
