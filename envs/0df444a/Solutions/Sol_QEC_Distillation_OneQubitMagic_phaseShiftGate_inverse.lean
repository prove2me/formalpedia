-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseShiftGate_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:17:44.437279+00:00
-- url     : https://prove2.me/submissions/c04feff6-cf71-4ae8-8cad-0073579cac4c

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_mul_neg

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution (theta : Real) :
    (phaseShiftGate theta)⁻¹ = phaseShiftGate (-theta) :=
  (inv_eq_iff_mul_eq_one).2 (phaseShiftGate_mul_neg theta)
end QEC.Distillation.OneQubitMagic
