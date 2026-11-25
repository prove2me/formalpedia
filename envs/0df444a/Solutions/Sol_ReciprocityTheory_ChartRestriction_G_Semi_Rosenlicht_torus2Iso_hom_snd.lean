-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torus2Iso_hom_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:28:30.257074+00:00
-- url     : https://prove2.me/submissions/063f5f40-3d71-4699-976a-128ca25d43b7

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
namespace ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
theorem _root_.solution : (torus2Iso K X).hom ≫
    (snd (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        AddMonoidAlgebra K X →ₐ[K] AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X).toRingHom) ≫
          (torusIso K X).hom := by
  first
  | exact (isPullback_torus2 K X).isoPullback_hom_snd
  | (simp [torus2Iso]; done)
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
