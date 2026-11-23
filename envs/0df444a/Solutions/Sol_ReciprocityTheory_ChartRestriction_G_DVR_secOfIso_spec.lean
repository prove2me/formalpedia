-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:54.454692+00:00
-- url     : https://prove2.me/submissions/21fdf956-953d-4349-ad1b-647399ceb4a5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {Y : Scheme.{0}} {A B : LB Y} (u : LB.Iso A B) (t : LB.Sec B)
variable {u}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hu : u.IsGen) (hA : A.IsLB) (hB : B.IsLB) (a : A.ι) (b : B.ι) :
    rs (inf_le_left : A.U a ⊓ B.U b ≤ A.U a) ((secOfIso t hu hA hB).f a) = isoCand u t a b :=
  secOfIsoF_spec t hu hA hB a b
end ReciprocityTheory.ChartRestriction.G.DVR
