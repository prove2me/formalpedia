-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_sval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:25.033374+00:00
-- url     : https://prove2.me/submissions/a9104c4c-062e-4780-ad24-c1c8ed6fe133

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
theorem _root_.solution {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = sval s₁ r z J := by
  have hj : ∀ k, (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) : K₁ ⊕ K₂ → L.ι) k =
      J (r ≫ Sum.elim φ₁ (fun k => h ≫ φ₂ k) k) := by
    intro k; cases k <;> rfl
  have hcoh : LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k)) (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k))) := fun k₁ k₂ hk => by
    rw [hj, hj, hk]
  have H' := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) hcoh
  have hm1 : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) :=
    show r.base z ∈ (⋂ k, ((φ₁ k).base ⁻¹' (L.U (J (r ≫ φ₁ k)) : Set X))) from
      Set.mem_iInter.2 fun k => hJ (r ≫ φ₁ k)
  have hm2 : r z ∈ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    show r.base z ∈ (⋂ k, ((h ≫ φ₂ k).base ⁻¹' (L.U (J (r ≫ h ≫ φ₂ k)) : Set X))) from
      Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ₂ k)
  have hm : r z ∈ (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) := ⟨hm1, hm2⟩
  have hle2 : (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) ≤ h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) := inf_le_right.trans (wchart_comp_le φ₂ h (fun k => J (r ≫ h ≫ φ₂ k)))
  have hle1 : (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) ≤ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) := inf_le_left
  have l1 : gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) ((Y'.presheaf.map (homOfLE hle2).op).hom ((h.app _).hom (s₂.f (fun k => J (r ≫ h ≫ φ₂ k))))) =
      gs (r ≫ h) z (LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k))) (s₂.f (fun k => J (r ≫ h ≫ φ₂ k))) :=
    (gs_res r z hle2 hm _).trans (gs_pull r h z _ (hle2 hm) _)
  have l2 : gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) (resTop (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) 1 * (Y'.presheaf.map (homOfLE hle1).op).hom (s₁.f (fun k => J (r ≫ φ₁ k)))) =
      gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k))) (s₁.f (fun k => J (r ≫ φ₁ k))) := by
    simp only [resTop, map_one]
    rw [_root_.one_mul]
    exact gs_res r z hle1 hm _
  have key := congrArg (gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)))) H'
  have e : (fun k => J ((r ≫ h) ≫ φ₂ k)) = (fun k => J (r ≫ h ≫ φ₂ k)) := by
    funext k; rw [Category.assoc]
  show gs (r ≫ h) z (LB.wchart L φ₂ (fun k => J ((r ≫ h) ≫ φ₂ k)))
      (s₂.f (fun k => J ((r ≫ h) ≫ φ₂ k))) = gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k))) (s₁.f (fun k => J (r ≫ φ₁ k)))
  rw [e]
  exact l1.symm.trans (key.trans l2)
end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
