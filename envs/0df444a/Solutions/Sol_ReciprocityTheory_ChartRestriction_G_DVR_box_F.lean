-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.box_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:33.669449+00:00
-- url     : https://prove2.me/submissions/c2886c50-ac63-42d4-a3cc-172dae938a66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_box_sec_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_box_q

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
set_option maxHeartbeats 800000
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (P : UnifPowOf3 pD pA pG U' U) {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') {k : ℕ} {f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α}
    {f' : ∀ α' : D'.toPre.X, D'.toPre.SecB k α'} (hf' : IsBoxFamB pD k f' f) (α' : D'.toPre.X) :
    (∏ a, omB pD y J J' ((pGl U'.toUnifPre e) ≫ D'.toPre.famφB α' a) ^ DegPre.famε k a).val * sval (f' α') (pGl U'.toUnifPre e) y J' =
      ∏ i, sval (f i (pD.xe α' i)) (rhoE I pG e i ≫ (pGl U.toUnifPre e)) y J := by
  obtain ⟨hφ, H⟩ := hf' α'
  have := box_sec_val pD.w hφ (f' α') (fun i => f i (pD.xe α' i)) _ H (pGl U'.toUnifPre e) y hJ hJ'
  simp only [box_q P] at this
  exact this
end ReciprocityTheory.ChartRestriction.G.DVR
