-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_TB_ValAt_valAt__sub_69b16cdcbcca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:53:07.568457+00:00
-- url     : https://prove2.me/submissions/000d1bf9-2fcf-4884-8144-d7973831834b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.ValAt
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.TB.ValAt
theorem _root_.solution (x : Sp ℂ ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valAt' x U (f - g) = valAt' x U f - valAt' x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp [valAt'_of _ _ h, valAt]
  · simp [valAt'_of_not _ _ h]
end ReciprocityTheory.ChartRestriction.G.TB.ValAt
