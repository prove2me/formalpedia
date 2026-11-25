-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.anX_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:16:15.361805+00:00
-- url     : https://prove2.me/submissions/2ff6f2de-f4f9-45c5-a6e3-902843f1d411

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_one_left___d591b489c5c3
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anX_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_ex_zero_eq_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_aug


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
variable [Algebra c.F ℂ]
variable (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
  (y : FrPt Xo c ℂ) (hy : y.x = F.u i P)
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (m : ℕ) :
    homAt y.x (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) ≫ anX F i P hP y hy m = 1 := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, anX_left]
  refine (jetPt_aug (anE F i P) (anHol F i P hP) m).trans ?_
  show (F.ex i P 0).left = _
  rw [ex_zero_eq_one F i P hP, one_left'', one_left'']
  congr 1
  rw [← hy]
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by
    first
      | simp [spMap]
      | (simp only [spMap]
         rw [show CommRingCat.ofHom (RingHom.id ℂ) = 𝟙 _ from rfl, Spec.map_id])
  simp [overAt, hid]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
