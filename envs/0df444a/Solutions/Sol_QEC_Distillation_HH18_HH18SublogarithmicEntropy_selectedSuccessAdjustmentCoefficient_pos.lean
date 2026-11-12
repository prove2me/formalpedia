-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.selectedSuccessAdjustmentCoefficient_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:15:14.206198+00:00
-- url     : https://prove2.me/submissions/bf58bef1-7668-4ec0-84f3-01ccb4f096a0

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
section
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology
private theorem rawSuccessAdjustmentCoefficient_pos {q sigma : ℝ} {n k d : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hsigma : 0 < sigma) :
    0 < rawSuccessAdjustmentCoefficient q sigma n k d := by
  have hone_div : 1 < (1 / q) := by
    apply (lt_div_iff₀ hq0).2
    nlinarith
  have hlogq : 0 < Real.log (1 / q) := Real.log_pos hone_div
  unfold rawSuccessAdjustmentCoefficient
  exact div_pos (one_div_pos.mpr hsigma)
    (Real.rpow_pos_of_pos hlogq _)
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
end

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution {q sigma : ℝ} {A D j : Nat}
    (hq0 : 0 < q) (hq1 : q < 1) (hsigma : 0 < sigma) :
    0 < selectedSuccessAdjustmentCoefficient q sigma A D j := by
  unfold selectedSuccessAdjustmentCoefficient
  exact rawSuccessAdjustmentCoefficient_pos hq0 hq1 hsigma
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
