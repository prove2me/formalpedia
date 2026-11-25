-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.aug_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:48.884463+00:00
-- url     : https://prove2.me/submissions/c3cd9427-5a37-4662-bfdd-d936cbc4d5d7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zero_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_eq_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR epsScaleR IsTangent IsLieComb IsLieBasis)
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {κ : Type} {d m : ℕ} (ψ : JetR R (Fin d) m →ₐ[R] JetR R κ m) :
    (jetAug R κ m).comp ψ = jetAug R (Fin d) m ↔ ∀ j, jetZeroR R κ m (ψ (zR m j)) = 0 := by
  constructor
  · intro h j
    apply jetAug_zero_injective κ
    rw [map_zero, ← AlgHom.comp_apply, ← jetAug_eq_comp, ← AlgHom.comp_apply, h, jetAug_zR]
  · intro h
    apply jet_ext
    intro j
    rw [AlgHom.comp_apply, jetAug_eq_comp, AlgHom.comp_apply, h j, map_zero, jetAug_zR]
end ReciprocityTheory.ChartRestriction.G.Chart
