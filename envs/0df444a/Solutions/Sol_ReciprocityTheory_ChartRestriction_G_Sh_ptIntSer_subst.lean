-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:02.634808+00:00
-- url     : https://prove2.me/submissions/2597c77f-a758-4e29-99e6-b2d0d258d261

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution {σ τ : Type*} {A : σ → MvPowerSeries τ C} (hA : HasSubst A)
    (hAi : ∀ s, A s ∈ ptIntSer v τ) {f : MvPowerSeries σ C} (hf : f ∈ ptIntSer v σ) :
    subst A f ∈ ptIntSer v τ := by
  intro e
  rw [MvPowerSeries.coeff_subst hA f e]
  have hmem : ∀ d : σ →₀ ℕ, coeff d f • coeff e (d.prod fun s n => A s ^ n) ∈ ptIntSub v := by
    intro d
    rw [smul_eq_mul]
    refine Subring.mul_mem _ (hf d) ?_
    have hp : (d.prod fun s n => A s ^ n) ∈ ptIntSer v τ :=
      Subring.prod_mem _ fun s _ => Subring.pow_mem _ (hAi s) _
    exact hp e
  have key : ∀ g : (σ →₀ ℕ) → C, (∀ i, g i ∈ ptIntSub v) → ∑ᶠ i, g i ∈ ptIntSub v := by
    intro g hg
    by_cases hfin : (Function.support g).Finite
    · rw [finsum_eq_sum g hfin]
      exact Subring.sum_mem _ fun i _ => hg i
    · rw [finsum_of_infinite_support hfin]
      exact Subring.zero_mem _
  exact key _ hmem
end ReciprocityTheory.ChartRestriction.G.Sh
