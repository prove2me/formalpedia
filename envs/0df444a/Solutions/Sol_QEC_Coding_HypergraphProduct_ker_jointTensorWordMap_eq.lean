-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.ker_jointTensorWordMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:36:37.163195+00:00
-- url     : https://prove2.me/submissions/d5fb4472-cbab-4b28-9932-2024c115a472

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {F : Type v} {A A' B B' : Type u}
    [Field F] [Fintype B] [DecidableEq B]
    [Fintype B'] [DecidableEq B']
    (f : Word F A →ₗ[F] Word F A') (g : Word F B →ₗ[F] Word F B') :
    LinearMap.ker (jointTensorWordMap f g) =
      LinearMap.ker (jointTensorMap f g) := by
  unfold jointTensorWordMap
  exact LinearEquiv.ker_comp _ _
end QEC.Coding.HypergraphProduct
