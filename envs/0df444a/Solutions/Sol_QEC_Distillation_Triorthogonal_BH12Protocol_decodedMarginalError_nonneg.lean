-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.decodedMarginalError_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T19:49:42.29663+00:00
-- url     : https://prove2.me/submissions/04247054-a945-4ea7-8251-e72a2b0a1b8c

import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_rawMarginalErrorWeight_nonneg
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem solution (q : Nat) (p : ErrorParameter)
    (hpos : 0 < rawSuccessMass q p) (a : OddRow q) :
    0 ≤ decodedMarginalError q p hpos a := by
  simp only [decodedMarginalError, dif_pos hpos]
  exact div_nonneg (rawMarginalErrorWeight_nonneg q p a) hpos.le