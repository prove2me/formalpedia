-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_of_sval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:02.54675+00:00
-- url     : https://prove2.me/submissions/b492fd88-11ef-46c1-a0d3-189079457609

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
theorem _root_.solution (hL : L.IsLB) {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    (H : ∀ (y : Y') (J : (Y' ⟶ X) → L.ι), Good L y J → sval s₂ (𝟙 Y' ≫ h) y J = sval s₁ (𝟙 Y') y J) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1 := by
  intro j₁ j₂ hc
  simp only [resTop, map_one, _root_.one_mul]
  refine fn_ext fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := exists_good L hL y _ _ hc (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hy.1 a, Set.mem_iInter.1 hy.2 a])
  have := H y J hJ
  rw [sval_of s₁ _ y J j₁ (fun k => by rw [Category.id_comp]; exact e (.inl k)),
    sval_of s₂ _ y J j₂ (fun k => by rw [Category.id_comp]; exact e (.inr k))] at this
  have le : LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤ h ⁻¹ᵁ LB.wchart L φ₂ j₂ :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  exact ((gs_res _ y _ hy _).trans (gs_pull _ h y _ (le hy.2) _)).trans (this.trans (gs_res _ y _ hy _).symm)
end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
