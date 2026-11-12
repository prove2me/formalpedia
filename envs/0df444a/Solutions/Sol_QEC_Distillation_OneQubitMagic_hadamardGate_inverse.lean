-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hadamardGate_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:17:28.769223+00:00
-- url     : https://prove2.me/submissions/8b33c185-ad90-44e2-be71-292814b27c46

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_mul_self

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution : hadamardGate⁻¹ = hadamardGate :=
  (inv_eq_iff_mul_eq_one).2 hadamardGate_mul_self
end QEC.Distillation.OneQubitMagic
