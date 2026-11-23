-- Prove2me | solution 1 for P2M_GlobalTheory_KernelNoTorsion_torsion__pow_0f791edbd64c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:19.549318+00:00
-- url     : https://prove2.me/submissions/5d981c4e-c856-4b90-8441-ce218cd500e7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KernelNoTorsion
namespace GlobalTheory.KernelNoTorsion
theorem _root_.solution {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) :
    torsion.ι G n ^ n = 1 := by
  rw [← comp_mulN, Hom.one_def]
  refine (pullback.condition).trans ?_
  congr 1
  exact toUnit_unique _ _
end GlobalTheory.KernelNoTorsion
