-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.epsilonStar_rational_bracket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:28:31.948834+00:00
-- url     : https://prove2.me/submissions/d2b12fdc-31d1-4f07-8760-16873c4dde29

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
section
noncomputable section
namespace QEC
namespace Distillation
namespace BK15
namespace Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic
private theorem bk15BiasStar_between_rational_endpoints :
    bk15BiasUpper < bk15BiasStar ∧ bk15BiasStar < bk15BiasLower := by
  rcases exists_interior_bias_fixedPolynomial_root with
    ⟨bias, hupper, hlower, hroot⟩
  have hbias_pos : 0 < bias := by
    have hendpoint : 0 < bk15BiasUpper := by
      norm_num [bk15BiasUpper]
    linarith
  have hbias_one : bias < 1 := by
    have hendpoint : bk15BiasLower < 1 := by
      norm_num [bk15BiasLower]
    linarith
  have heq : bias = bk15BiasStar :=
    fixedPolynomial_root_unique_in_unitInterval
      hbias_pos hbias_one bk15BiasStar_pos bk15BiasStar_lt_one
      hroot bk15FixedPolynomial_biasStar
  rw [heq] at hupper hlower
  exact ⟨hupper, hlower⟩
namespace BK15SemanticSchedule
end BK15SemanticSchedule
end Threshold
end BK15
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic
namespace QEC.Distillation.BK15.Threshold
theorem _root_.solution :
    14147 / 100000 < epsilonStar ∧ epsilonStar < 14149 / 100000 := by
  have hbounds := bk15BiasStar_between_rational_endpoints
  unfold epsilonStar
  constructor
  · calc
      (14147 : Real) / 100000 = (1 - bk15BiasLower) / 2 := by
        norm_num [bk15BiasLower]
      _ < (1 - bk15BiasStar) / 2 := by linarith [hbounds.2]
  · calc
      (1 - bk15BiasStar) / 2 < (1 - bk15BiasUpper) / 2 := by
        linarith [hbounds.1]
      _ = (14149 : Real) / 100000 := by
        norm_num [bk15BiasUpper]
end QEC.Distillation.BK15.Threshold
