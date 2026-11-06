-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.evaluationZeroOn_iff_mem_riemannRochSubmodule_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:42:09.558202+00:00
-- url     : https://prove2.me/submissions/c74d5e76-c559-48b5-8a4a-cc6048357032

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationKernel
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationZeroOn_mem_riemannRochSubmodule_sub


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
noncomputable section
variable {k F ι : Type*} [Field k] [Finite k] [Field F] [Algebra k F] [Fintype ι]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (S : Finset ι)
    (f : GlobalPlace.riemannRochSubmodule G) :
    (∀ j ∈ S, agEvaluationLinearMap G Q hG f j = 0) ↔
      (f : F) ∈ GlobalPlace.riemannRochSubmodule (G - zeroCoordinateDivisor Q S) :=
  ⟨evaluationZeroOn_mem_riemannRochSubmodule_sub G Q hQ hG S f,
    evaluationZeroOn_of_mem_riemannRochSubmodule_sub G Q hQ hG S f⟩
end QEC.Coding.AlgebraicGeometry
