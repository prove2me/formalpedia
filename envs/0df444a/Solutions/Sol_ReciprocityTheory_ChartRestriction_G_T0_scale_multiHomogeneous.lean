-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.scale_multiHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:49.151368+00:00
-- url     : https://prove2.me/submissions/9f26aea1-e02a-478c-ac59-950011880e2b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scaleEquiv_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (b : Fin (D + 1)) (u : Kˣ) (a : Fin (D + 1) → ℕ)
    (F : MvPolynomial (TVar D N) K) (hF : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a F) :
    scaleEquiv (fun v : TVar D N => v.1 = b) u F = C ((u : K) ^ a b) * F := by
  have hsum : ∀ s : TVar D N →₀ ℕ,
      (∑ v ∈ Finset.univ.filter (fun v : TVar D N => v.1 = b), s v) = ∑ j, s (b, j) := by
    intro s
    rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single b]
    · simp
    · intro x _ hx
      simp [hx]
    · intro h
      exact absurd (Finset.mem_univ b) h
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [scaleEquiv_monomial, hsum s, hF s hs b]
end ReciprocityTheory.ChartRestriction.G.T0
