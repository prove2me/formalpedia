-- Prove2me | solution 1 for P2M_GlobalTheory_VeryAmplePow_sec_trans__22f5df49d8af
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:03.25074+00:00
-- url     : https://prove2.me/submissions/4c5c86d8-53b3-4df1-baec-0a9fc5c7658e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
namespace GlobalTheory.VeryAmplePow
theorem _root_.solution {Z Y : Scheme.{0}} {M : LB Y} (s : LB.Sec M) (r : Z ⟶ Y) (z : Z) {j j' : M.ι}
    (hj : r z ∈ M.U j) (hj' : r z ∈ M.U j') :
    gs r z (M.U j) (s.f j) = (gm r z _ (M.g j j')).val * gs r z (M.U j') (s.f j') := by
  have hm : r z ∈ M.U j ⊓ M.U j' := ⟨hj, hj'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat j j')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))
end GlobalTheory.VeryAmplePow
