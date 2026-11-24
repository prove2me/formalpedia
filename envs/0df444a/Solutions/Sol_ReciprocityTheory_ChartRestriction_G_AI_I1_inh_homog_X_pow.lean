-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_homog_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:45.936542+00:00
-- url     : https://prove2.me/submissions/32856cfc-12f3-4a68-a617-d93638663bd0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*}
  [Field F]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (p : Σ k, ι k) (m : ℕ) :
    IsMultiHomog (X p ^ m : MRingOver F ι) (Pi.single p.1 m) := by
  classical
  intro n hn k
  rw [support_X_pow, Finset.mem_singleton] at hn
  subst hn
  obtain ⟨k', i'⟩ := p
  by_cases hk : k = k'
  · subst hk
    rw [Finset.sum_eq_single i']
    · simp
    · intro b _ hb; rw [Finsupp.single_apply, if_neg]; intro h; exact hb (sigma_mk_injective h).symm
    · simp
  · rw [Pi.single_apply, if_neg hk]
    apply Finset.sum_eq_zero
    intro b _
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hk (congrArg Sigma.fst h).symm
end ReciprocityTheory.ChartRestriction.G.AI.I1
