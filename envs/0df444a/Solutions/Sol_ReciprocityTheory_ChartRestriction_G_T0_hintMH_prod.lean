-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hintMH_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:16:00.577701+00:00
-- url     : https://prove2.me/submissions/f714bf96-c93b-49ab-bfc2-683b52b0f657

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ComponentFormProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintIntOfBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintLogFinprod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hintMH_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hintMH_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hintMH_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {R ι : Type*} [CommSemiring R] {D n : ℕ} (s : Finset ι)
    (q : ι → MvPolynomial (Fin (D + 1) × Fin n) R) (m : ι → ℕ) (hq : ∀ p ∈ s, HintMH (q p)) :
    HintMH (∏ p ∈ s, q p ^ m p) := by
  exact Finset.prod_induction _ (fun x => HintMH x) (fun a b ha hb => hintMH_mul ha hb) hintMH_one
    (fun p hp => hintMH_pow (hq p hp) (m p))
end ReciprocityTheory.ChartRestriction.G.T0
