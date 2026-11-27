-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.finsum_log_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:29:41.23979+00:00
-- url     : https://prove2.me/submissions/c16c892e-8520-4ca0-a172-498a625d172a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Qdist
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Mathlib.NumberTheory.Height.NumberField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution {α : Type*} (f : α → ℝ) (hpos : ∀ a, 0 < f a)
    (hf : (Function.mulSupport f).Finite) : ∑ᶠ a, Real.log (f a) = Real.log (∏ᶠ a, f a) := by
  have h1 : Function.support (fun a => Real.log (f a)) ⊆ (hf.toFinset : Set α) := by
    intro a ha
    rw [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h
    exact (Function.mem_support.mp ha) (by rw [h, Real.log_one])
  have h2 : Function.mulSupport f ⊆ (hf.toFinset : Set α) := by
    rw [Set.Finite.coe_toFinset]
  rw [finsum_eq_sum_of_support_subset _ h1, finprod_eq_prod_of_mulSupport_subset _ h2]
  exact (Real.log_prod fun a _ => (hpos a).ne').symm
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
