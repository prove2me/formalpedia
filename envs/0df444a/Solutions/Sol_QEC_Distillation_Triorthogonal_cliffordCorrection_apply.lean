-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.cliffordCorrection_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:54:28.043235+00:00
-- url     : https://prove2.me/submissions/a9eb28fd-6be0-44cd-97f7-14db8a75943b

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_composeAtoms_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_atomAngleSum_correctionAtoms

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
namespace QEC.Distillation.Triorthogonal
theorem _root_.solution
    (single : Index → ZMod 4) (pair : Index → Index → ZMod 2)
    (psi : Qubit.QubitRegister Index) (bits : Qubit.Bitstring Index) :
    cliffordCorrection single pair psi bits =
      OneQubitMagic.phaseAmplitude (cliffordCorrectionAngle single pair bits) * psi bits := by
  rw [cliffordCorrection, composeAtoms_apply, atomAngleSum_correctionAtoms]
end QEC.Distillation.Triorthogonal
