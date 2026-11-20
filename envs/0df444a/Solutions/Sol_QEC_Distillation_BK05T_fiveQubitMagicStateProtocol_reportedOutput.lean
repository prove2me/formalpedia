-- Prove2me | solution 1 for QEC.Distillation.BK05T.fiveQubitMagicStateProtocol_reportedOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:16:36.797486+00:00
-- url     : https://prove2.me/submissions/fafc4b5c-d83f-4f95-89b7-1083898a61a4

import Theorems.Thm_QEC_Distillation_BK05T_fiveQubitDistillationRun_acceptedOutput

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open OneQubitMagic
open scoped BigOperators ComplexOrder TensorProduct
attribute [local irreducible] fiveQubitPreparedRowScalar
attribute [local irreducible] GaussianInt.toComplex
attribute [local irreducible] arrayTarget
namespace QEC.Distillation.BK05T
theorem _root_.solution
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitMagicStateProtocol epsilon hzero hone).run.reportedOutput
        (fiveQubitMagicStateProtocol epsilon hzero hone).behavior =
      fiveQubitAcceptedOutput epsilon hzero hone := by
  change (fiveQubitDistillationRun epsilon hzero hone).acceptedOutput = _
  exact fiveQubitDistillationRun_acceptedOutput epsilon hzero hone
end QEC.Distillation.BK05T
