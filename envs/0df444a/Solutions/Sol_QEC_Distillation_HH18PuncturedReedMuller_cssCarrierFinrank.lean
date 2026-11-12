-- Prove2me | solution 1 for QEC.Distillation.HH18PuncturedReedMuller.cssCarrierFinrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:29:50.002989+00:00
-- url     : https://prove2.me/submissions/62bc8b3c-f15e-48b2-965b-72371bf7746c

import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_cssLogicalExponent
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSQuantumCodeOfDualLe_finrank_carrier


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
    Module.finrank Complex (cssCode h).stabilizer.code.carrier =
      2 ^ binomialUpTo m w := by
  rw [show (cssCode h).stabilizer.code =
      binaryCSSQuantumCodeOfDualLe (xCode w r m) (zCode w r m)
        (cssDualContainment h) by rfl]
  rw [binaryCSSQuantumCodeOfDualLe_finrank_carrier,
    cssLogicalExponent h]
end QEC.Distillation.HH18PuncturedReedMuller
