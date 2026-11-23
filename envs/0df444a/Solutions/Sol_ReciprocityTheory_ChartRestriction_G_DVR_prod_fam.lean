-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.prod_fam
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:25.955649+00:00
-- url     : https://prove2.me/submissions/3d0d3cf2-7e2d-489a-98a7-9f8985f97555

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F) (α : D.X) (k : ℕ) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ DegPre.famφ D F α i) ^ DegPre.famε k i =
      h (ρ ≫ DegPre.prB D F).left ^ ((k : ℤ) - 1) * h (cP D T α * (ρ ≫ DegPre.prB D F)).left * (h (cP D T α).left)⁻¹ *
        h (1 : T ⟶ D.P.A).left := by
  have e₁ : ρ.left ≫ DegPre.famφ D F α 1 = (cP D T α * (ρ ≫ DegPre.prB D F)).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (DegPre.prB D F) (cP D _ α)).trans (by rw [comp_cP, mul_comm]))
  have e₂ : ρ.left ≫ DegPre.famφ D F α 2 = (cP D T α).left := congrArg (fun q => q.left) (comp_cP D ρ α)
  have e₃ : ρ.left ≫ DegPre.famφ D F α 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl
end ReciprocityTheory.ChartRestriction.G.DVR
