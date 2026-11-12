-- Prove2me | solution 1 for QEC.Distillation.HH18PuncturedReedMuller.logicalZPauli_commutes_xCheck
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:27:54.828752+00:00
-- url     : https://prove2.me/submissions/43526ec8-1f47-4f74-909e-e63123ad7f02

import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_logicalBasisWord_mem_xDual

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
    (h : Admissible w r m) (logical : LogicalSite m w)
    {x : Word (ZMod 2) (PhysicalSite m w)}
    (hx : x ∈ (xCode w r m).carrier) :
    PauliSymplectic.Commutes (logicalZPauli h logical) (cssXCheck x) :=
  cssZCheck_commutes_cssXCheck_of_mem_dual (xCode w r m)
    hx (logicalBasisWord_mem_xDual h logical)
end QEC.Distillation.HH18PuncturedReedMuller
