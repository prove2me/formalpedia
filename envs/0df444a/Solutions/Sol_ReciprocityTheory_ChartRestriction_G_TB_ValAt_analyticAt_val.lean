-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ValAt.analyticAt_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:32:25.670223+00:00
-- url     : https://prove2.me/submissions/703218dc-c1ef-449b-a61e-cbf357b5b27c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


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
open NumberField
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.ValAt
theorem _root_.solution (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (hol : ∀ (U : X.Opens) (f : Γ(X, U)), IsOpen {z | ⊤ ≤ e z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (e z) U f) {z | ⊤ ≤ e z ⁻¹ᵁ U})
    (U : X.Opens) (f : Γ(X, U)) (z₀ : Fin g → ℂ) (h0 : ⊤ ≤ e z₀ ⁻¹ᵁ U) :
    AnalyticAt ℂ (fun z => valAt' (e z) U f) z₀ :=
  ReciprocityTheory.AnForm.Osgood.osgood g {z | ⊤ ≤ e z ⁻¹ᵁ U} (fun z => valAt' (e z) U f) (hol U f).1 (hol U f).2 z₀ h0
end ReciprocityTheory.ChartRestriction.G.TB.ValAt
