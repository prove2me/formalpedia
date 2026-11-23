-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.sval_pullSec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:17.074338+00:00
-- url     : https://prove2.me/submissions/783de50a-f990-4603-b3d7-4f0b79c11443

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation

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
theorem _root_.solution {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval (pullSec L φ ε s h) r z J = sval s (r ≫ h) z J := by
  have hmem : r z ∈ LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) := by
    show r.base z ∈ (⋂ k, ((h ≫ φ k).base ⁻¹' (L.U (J (r ≫ h ≫ φ k)) : Set X)))
    exact Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  calc sval (pullSec L φ ε s h) r z J
      = gs r z (LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)))
          ((Y'.presheaf.map (homOfLE (wchart_comp_le φ h (fun k => J (r ≫ h ≫ φ k)))).op).hom
            ((h.app _).hom (s.f (fun k => J (r ≫ h ≫ φ k))))) := rfl
    _ = gs r z (h ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)))
          ((h.app _).hom (s.f (fun k => J (r ≫ h ≫ φ k)))) :=
        gs_res r z (wchart_comp_le φ h _) hmem _
    _ = gs (r ≫ h) z (LB.wchart L φ (fun k => J (r ≫ h ≫ φ k))) (s.f (fun k => J (r ≫ h ≫ φ k))) :=
        gs_pull r h z _ (wchart_comp_le φ h _ hmem) _
    _ = sval s (r ≫ h) z J := by
        have e : (fun k => J ((r ≫ h) ≫ φ k)) = fun k => J (r ≫ h ≫ φ k) := by
          funext k; rw [Category.assoc]
        show _ = gs (r ≫ h) z (LB.wchart L φ (fun k => J ((r ≫ h) ≫ φ k)))
          (s.f (fun k => J ((r ≫ h) ≫ φ k)))
        rw [e]
end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
