-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ValAt.famHol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:38.506643+00:00
-- url     : https://prove2.me/submissions/7f50f600-4c92-47bb-928c-2e6e961fd8ed

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ValAt_hol_of_isHolTo

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
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)} (W : FamilyUnif Xo σ ty) (i : Fin W.n)
    (P : (W.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (W.Di i) ty P) (U : Xo.univ.t.G.left.Opens)
    (f : Γ(Xo.univ.t.G.left, U)) :
    IsOpen {z | ⊤ ≤ (W.ex i P z).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (W.ex i P z).left U f) {z | ⊤ ≤ (W.ex i P z).left ⁻¹ᵁ U} :=
  hol_of_isHolTo (fun z => (W.ex i P z).left)
    (W.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2 U f
end ReciprocityTheory.ChartRestriction.G.TB.ValAt
