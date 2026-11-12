-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseGate_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:57:38.42007+00:00
-- url     : https://prove2.me/submissions/b01aa9aa-aaa5-4f00-b47d-93899f72d26f

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_mul_phaseInverseGate

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution : phaseGate⁻¹ = phaseInverseGate :=
  (inv_eq_iff_mul_eq_one).2 phaseGate_mul_phaseInverseGate
end QEC.Distillation.OneQubitMagic
