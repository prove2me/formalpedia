-- Prove2me | solution 1 for QEC.Distillation.HH18PuncturedReedMuller.cssParameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:33:17.804062+00:00
-- url     : https://prove2.me/submissions/ce8ead6f-3663-448b-a098-b4eb9748e976

import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_semanticDistance
import Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_cssLength
import Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_cssLogicalExponent
import Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_cssCarrierFinrank

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
theorem _root_.solution {w r m : Nat} (h : Admissible w r m) :
    Length (ZMod 2) (PhysicalSite m w) = binomialTail m w ∧
      Length (ZMod 2) (PhysicalSite m w) - Dimension (xCode w r m) -
          Dimension (zCode w r m) = binomialUpTo m w ∧
        Module.finrank Complex (cssCode h).stabilizer.code.carrier =
          2 ^ binomialUpTo m w ∧
        StabilizerCode.SemanticStabilizerDistance (sourceValidStabilizer h)
          (binomialTail (r + 1) w) :=
  ⟨cssLength h, cssLogicalExponent h, cssCarrierFinrank h, semanticDistance h⟩
end QEC.Distillation.HH18PuncturedReedMuller
