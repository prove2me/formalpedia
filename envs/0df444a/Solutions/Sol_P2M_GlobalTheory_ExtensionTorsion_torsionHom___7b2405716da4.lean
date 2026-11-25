-- Prove2me | solution 1 for P2M_GlobalTheory_ExtensionTorsion_torsionHom___7b2405716da4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:31:42.940851+00:00
-- url     : https://prove2.me/submissions/7d7afc36-04c9-4ee1-b9e7-710b2b01bde4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsFiniteFlatTorsionOfIsGt
import Theorems.Thm_P2M_GlobalTheory_KernelNoTorsion_torsionLift___104fe53c2c33


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.ExtensionTorsion
open KernelNoTorsion
variable {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
namespace GlobalTheory.ExtensionTorsion
theorem _root_.solution (q : G ⟶ B) [IsMonHom q] (N : ℕ) :
    torsionHom q N ≫ torsion.ι B N = torsion.ι G N ≫ q :=
  torsionLift_ι _ _
end GlobalTheory.ExtensionTorsion
