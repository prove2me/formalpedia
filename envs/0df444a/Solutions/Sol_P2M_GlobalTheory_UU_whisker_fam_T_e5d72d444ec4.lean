-- Prove2me | solution 1 for P2M_GlobalTheory_UU_whisker_fam_T_e5d72d444ec4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:05:23.449322+00:00
-- url     : https://prove2.me/submissions/0713014f-72dc-4dba-ae23-502177866732

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsPullSecSval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T T' : Over (Spec (CommRingCat.of R))}
    (ρ : T' ⟶ T) (α : D.X) (i : Fin 4) : (ρ ▷ D.P.A).left ≫ famφT D T α i = famφT D T' α i := by
  have hu : ρ ▷ D.P.A ≫ toUnit _ = toUnit _ := toUnit_unique _ _
  fin_cases i
  · show (ρ ▷ D.P.A ≫ snd T D.P.A).left = (snd T' D.P.A).left
    rw [whiskerRight_snd]
  · show (ρ ▷ D.P.A ≫ padd D.P.A (snd T D.P.A) (toUnit _ ≫ D.c α)).left =
      (padd D.P.A (snd T' D.P.A) (toUnit _ ≫ D.c α)).left
    congr 1
    unfold padd
    rw [← Category.assoc, comp_lift, whiskerRight_snd, ← Category.assoc, hu]
  · show (ρ ▷ D.P.A ≫ toUnit _ ≫ D.c α).left = (toUnit (T' ⊗ D.P.A) ≫ D.c α).left
    rw [← Category.assoc, hu]
  · show (ρ ▷ D.P.A ≫ toUnit _ ≫ η[D.P.A]).left = (toUnit (T' ⊗ D.P.A) ≫ η[D.P.A]).left
    rw [← Category.assoc, hu]
end GlobalTheory.UU
