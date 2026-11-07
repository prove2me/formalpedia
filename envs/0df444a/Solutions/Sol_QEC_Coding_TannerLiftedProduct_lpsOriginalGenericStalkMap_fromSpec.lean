-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGenericStalkMap_fromSpec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:17:19.666454+00:00
-- url     : https://prove2.me/submissions/1a296a17-0eac-4bc6-9a9a-daef41d44cbd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecFromStalk_transport

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {X Y : Scheme}
    (f : Y ⟶ X) (y : Y) (x : X) (h : f y = x) :
    Spec.map (eqToHom (congrArg X.presheaf.stalk h.symm) ≫ f.stalkMap y) ≫
      X.fromSpecStalk x = Y.fromSpecStalk y ≫ f := by
  rw [Spec.map_comp, Category.assoc, lpsOriginalSpecFromStalk_transport,
    Scheme.SpecMap_stalkMap_fromSpecStalk]
  exact h.symm
end QEC.Coding.TannerLiftedProduct
