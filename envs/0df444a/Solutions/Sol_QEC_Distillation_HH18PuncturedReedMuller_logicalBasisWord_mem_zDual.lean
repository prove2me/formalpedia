-- Prove2me | solution 1 for QEC.Distillation.HH18PuncturedReedMuller.logicalBasisWord_mem_zDual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:27:59.276798+00:00
-- url     : https://prove2.me/submissions/6e09cf2f-c4a6-4150-8ba1-d85f0eb63f55

import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Theorems.Thm_QEC_Coding_PuncturedReedMuller_shortenedReedMullerCode_dual_eq_punctured


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PuncturedReedMuller
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18PuncturedReedMuller
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w) :
    logicalBasisWord h logical ∈ (zCode w r m).dual.carrier := by
  change keptSystematicLift h (canonicalBasisWord logical) ∈
    (zCode w r m).dual.carrier
  rw [zCode_eq_shortened, shortenedReedMullerCode_dual_eq_punctured h]
  exact keptSystematicLift_mem_punctured h (canonicalBasisWord logical)
end QEC.Distillation.HH18PuncturedReedMuller
