-- Prove2me | solution 1 for P2M_GlobalTheory_LevelCompat_thickMap_O__cc5aa398615b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:30.157445+00:00
-- url     : https://prove2.me/submissions/2f3ec5ca-1e89-43f7-ac2c-6890427eaf65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GtCoordCompatOfPull
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_O__comp_24bcd133e28a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.LevelCompat
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.LevelCompat
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g₀ : GtCoord I D e G)
    (g₁ : GtCoord I D (e + 1) G) (hq : thickMap R I e G ≫ g₁.pG.left = g₀.pG.left) (χ : D.X) (k : Fin 4) :
    thickMap R I e G ≫ D.Oφ g₁.pG χ k = D.Oφ g₀.pG χ k := by
  have h : thickMapOver I e G ≫ g₁.pG = g₀.pG := Over.OverMorphism.ext hq
  rw [← h]
  exact WeightPf.Oφ_comp (thickMapOver I e G) g₁.pG χ k
end GlobalTheory.LevelCompat
