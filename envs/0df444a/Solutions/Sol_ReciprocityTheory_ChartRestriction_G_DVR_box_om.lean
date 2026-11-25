-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.box_om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:34.503232+00:00
-- url     : https://prove2.me/submissions/6dc93182-817c-424c-82cb-8bcd53f21d81

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι} (k : ℕ) (α' : D'.toPre.X) :
    (∏ a, omB pD y J J' ((pGl U'.toUnifPre e) ≫ D'.toPre.famφB α' a) ^ DegPre.famε k a) * ∏ a, omB pD y J J' (Oφl U'.toUnifPre e α' a) ^ Oinvε a =
      omB pD y J J' (pGl U'.toUnifPre e) ^ k := by
  have a₀ : (pGl U'.toUnifPre e) ≫ D'.toPre.famφB α' 0 = (pGl U'.toUnifPre e) := Category.comp_id _
  have a₁ : (pGl U'.toUnifPre e) ≫ D'.toPre.famφB α' 1 = Oφl U'.toUnifPre e α' 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul (U'.gt e).pG (𝟙 _) (cP D'.toPre _ α')).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D'.toPre _ α')))
  have a₂ : (pGl U'.toUnifPre e) ≫ D'.toPre.famφB α' 2 = Oφl U'.toUnifPre e α' 1 :=
    congrArg (fun z => z.left) (comp_cP D'.toPre (U'.gt e).pG α')
  have a₃ : (pGl U'.toUnifPre e) ≫ D'.toPre.famφB α' 3 = Oφl U'.toUnifPre e α' 3 :=
    congrArg (fun z : _ ⟶ D'.toPre.P.A => z.left) (MonObj.comp_one (M := D'.toPre.P.A) (U'.gt e).pG)
  have a₄ : Oφl U'.toUnifPre e α' 2 = (pGl U'.toUnifPre e) := rfl
  rw [Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]
  module
end ReciprocityTheory.ChartRestriction.G.DVR
