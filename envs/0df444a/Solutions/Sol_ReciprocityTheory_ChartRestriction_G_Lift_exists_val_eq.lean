-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lift.exists_val_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:39:57.093013+00:00
-- url     : https://prove2.me/submissions/939e89cf-f792-4a0c-8ddc-22084ac2213f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValApprox
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_RApprox
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lift_valuation_approximation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lift
namespace ReciprocityTheory.ChartRestriction.G.Lift
theorem _root_.solution {Ω : Type} [Field Ω] {ι : Type} [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ)))
    (hgen : ∀ i, ∃ x, v i x = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hind : ∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j)) (n : ι → ℤ) :
    ∃ x : Ω, ∀ i, v i x = ((Multiplicative.ofAdd (n i) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
  valuation_approximation Ω ι v hgen hind n
end ReciprocityTheory.ChartRestriction.G.Lift
