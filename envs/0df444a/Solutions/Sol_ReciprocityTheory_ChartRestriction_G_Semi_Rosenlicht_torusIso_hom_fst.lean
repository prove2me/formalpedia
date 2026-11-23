-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torusIso_hom_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:43.222974+00:00
-- url     : https://prove2.me/submissions/f323b93f-fc25-4b8d-8efb-5288baffa51c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj MonObj TensorProduct
open AddMonoidAlgebra
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
variable (K : Type u) [Field K] (X : Type u) [AddCommGroup X]
attribute [local instance] zuAlgebra
open scoped AlgebraMonoidAlgebra
namespace ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
theorem _root_.solution : (torusIso K X).hom ≫ torusFst (Spec (.of K)) X =
    Spec.map (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra ZU.{u} X) (AddMonoidAlgebra K X))) := by
  first
  | exact (isPullback_torus K X).isoPullback_hom_fst
  | (simp [torusIso, torusFst]; done)
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
