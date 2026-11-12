-- Prove2me | solution 1 for QEC.Distillation.HH18PuncturedReedMuller.logicalZPauli_commutes_zCheck
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:27:51.365207+00:00
-- url     : https://prove2.me/submissions/1fe3851d-5ef4-4de2-9c28-d94c257b9755

import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller

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
    {z : Word (ZMod 2) (PhysicalSite m w)}
    (_hz : z ∈ (zCode w r m).carrier) :
    PauliSymplectic.Commutes (logicalZPauli h logical) (cssZCheck z) :=
  cssZCheck_commutes_cssZCheck _ _
end QEC.Distillation.HH18PuncturedReedMuller
