-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.agWordStar_mem_agStarProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:43.246604+00:00
-- url     : https://prove2.me/submissions/f280a160-9648-40fd-9175-6f644d9d76c0

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Code

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution [Fintype k] (C D : LinearCode k ι)
    {x y : Word k ι} (hx : x ∈ C.carrier) (hy : y ∈ D.carrier) :
    agWordStar x y ∈ agStarProduct C D :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩
end QEC.Coding.AlgebraicGeometry
