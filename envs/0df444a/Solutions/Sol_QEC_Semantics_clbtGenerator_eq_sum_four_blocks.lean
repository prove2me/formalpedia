-- Prove2me | solution 1 for QEC.Semantics.clbtGenerator_eq_sum_four_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:02:54.298111+00:00
-- url     : https://prove2.me/submissions/0f9827d7-26d2-4503-9f9e-f230b08bc46a

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator

set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution
    (L : Superoperator H) (O P rho : Operator H) :
    L (O * rho) =
      clbtGeneratorBlockOne L O P rho +
      clbtGeneratorBlockTwo L O P rho +
      clbtGeneratorBlockThree L O P rho +
      clbtGeneratorBlockFour L O P rho := by
  have hinput : O * rho = O * P * rho + O * (1 - P) * rho := by
    noncomm_ring
  have hout (A : Operator H) : L A = P * L A + (1 - P) * L A := by
    noncomm_ring
  rw [hinput, map_add, hout (O * P * rho), hout (O * (1 - P) * rho)]
  unfold clbtGeneratorBlockOne clbtGeneratorBlockTwo
    clbtGeneratorBlockThree clbtGeneratorBlockFour
  noncomm_ring
end QEC.Semantics
