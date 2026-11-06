-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.agEvaluationLinearMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:22:32.255197+00:00
-- url     : https://prove2.me/submissions/0127d114-295d-4c39-a7b3-6ffedf301689

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_NegativeDegreeVanishing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (G : Divisor (GlobalPlace k F))
    (Q : ι → RationalPlace k F) (hG : ∀ i, G (Q i).place = 0)
    (f : GlobalPlace.riemannRochSubmodule G) (i : ι) :
    agEvaluationLinearMap G Q hG f i =
      (Q i).evaluateRegular (f : F) (evaluationRegularity G Q hG f i) :=
  rfl
end QEC.Coding.AlgebraicGeometry
