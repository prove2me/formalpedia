-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.CliffordCorrectionAtom.realized_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:28:33.074608+00:00
-- url     : https://prove2.me/submissions/7c1059cd-da2c-45c6-91c4-142efc6d5c00

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal

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
open QEC.Distillation.Triorthogonal.CliffordCorrectionAtom
namespace QEC.Distillation.Triorthogonal.CliffordCorrectionAtom
theorem _root_.solution (a : CliffordCorrectionAtom Index)
    (psi : Qubit.QubitRegister Index) (bits : Qubit.Bitstring Index) :
    a.realized psi bits = OneQubitMagic.phaseAmplitude (a.angle bits) * psi bits := by
  cases a <;> rfl
end QEC.Distillation.Triorthogonal.CliffordCorrectionAtom
