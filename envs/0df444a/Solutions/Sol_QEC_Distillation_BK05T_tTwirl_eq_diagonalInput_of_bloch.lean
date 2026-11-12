-- Prove2me | solution 1 for QEC.Distillation.BK05T.tTwirl_eq_diagonalInput_of_bloch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:33:30.39551+00:00
-- url     : https://prove2.me/submissions/e4152e60-37e7-42b8-8e34-7343ed82c12c

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Theorems.Thm_QEC_Distillation_BK05T_tDiagonalInput_toOperator_eq_blochProjector
import Theorems.Thm_QEC_Distillation_BK05T_tTwirl_toOperator_eq_blochProjector_average
section
noncomputable section
namespace QEC
namespace Distillation
namespace BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
open scoped BigOperators
private theorem densityOperator_ext
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl
end BK05T
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
open scoped BigOperators
namespace QEC.Distillation.BK05T
theorem _root_.solution
    (rho : DensityOperator QubitSpace) (r : PauliAxis → Real)
    (hrho : rho.toOperator = blochProjector r)
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (hdiagonal : tTwirlBloch r = tDiagonalBloch epsilon) :
    tTwirl rho = tDiagonalInput epsilon hzero hone := by
  apply densityOperator_ext
  rw [tTwirl_toOperator_eq_blochProjector_average rho r hrho,
    tDiagonalInput_toOperator_eq_blochProjector]
  rw [hdiagonal]
end QEC.Distillation.BK05T
