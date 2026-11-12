-- Prove2me | solution 1 for QEC.Distillation.HH18PuncturedReedMuller.logicalXPauli_commutes_xCheck
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:27:30.271344+00:00
-- url     : https://prove2.me/submissions/5dbdd836-355f-4b0d-98d9-93e2a548b72d

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
    {x : Word (ZMod 2) (PhysicalSite m w)}
    (_hx : x ∈ (xCode w r m).carrier) :
    PauliSymplectic.Commutes (logicalXPauli h logical) (cssXCheck x) :=
  cssXCheck_commutes_cssXCheck _ _
end QEC.Distillation.HH18PuncturedReedMuller
