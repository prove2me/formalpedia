-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.trPt_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:03.972564+00:00
-- url     : https://prove2.me/submissions/1c076186-22b7-4cfd-a8c3-c25cea9e840c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowAlg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_FinOrdExists
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution (m m' : TF (R := R) F ⟶ D.P.A) :
    DegPre.trPt D F m ≫ DegPre.trPt D F m' = DegPre.trPt D F (m * m') := by
  have cm : ∀ (f : DegPre.BF D F ⟶ DegPre.BF D F) (g h : DegPre.BF D F ⟶ D.P.A),
      f ≫ (g * h) = (f ≫ g) * (f ≫ h) := by
    intro f g h
    show f ≫ (lift g h ≫ μ) = lift (f ≫ g) (f ≫ h) ≫ μ
    rw [comp_lift_assoc]
  have ca : ∀ (f : DegPre.BF D F ⟶ TF (R := R) F) (g h : TF (R := R) F ⟶ D.P.A),
      f ≫ (g * h) = (f ≫ g) * (f ≫ h) := by
    intro f g h
    show f ≫ (lift g h ≫ μ) = lift (f ≫ g) (f ≫ h) ≫ μ
    rw [comp_lift_assoc]
  have hB : ∀ m₀ : TF (R := R) F ⟶ D.P.A,
      lift (fst (TF (R := R) F) D.P.A) (padd D.P.A (D.prB F) (fst (TF (R := R) F) D.P.A ≫ m₀)) ≫ D.prB F =
        D.prB F * (fst (TF (R := R) F) D.P.A ≫ m₀) := by
    intro m₀
    first
      | exact lift_snd _ _
      | (simp only [DegPre.prB, lift_snd]; rfl)
      | (simp [DegPre.prB]; rfl)
  simp only [DegPre.trPt]
  rw [comp_lift, lift_fst]
  congr 1
  show lift _ _ ≫ (D.prB F * (fst _ _ ≫ m')) = D.prB F * (fst _ _ ≫ (m * m'))
  rw [cm, hB, lift_fst_assoc, ca, _root_.mul_assoc]
end ReciprocityTheory.ChartRestriction.G.H1
