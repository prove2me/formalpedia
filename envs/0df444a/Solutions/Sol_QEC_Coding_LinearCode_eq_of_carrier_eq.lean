-- Prove2me | solution 1 for QEC.Coding.LinearCode.eq_of_carrier_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:10:38.687187+00:00
-- url     : https://prove2.me/submissions/4067a4a3-4f18-4b21-9e4b-241e67b30858

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Duality

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.LinearCode
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.LinearCode
theorem _root_.solution {C D : LinearCode F ι} (h : C.carrier = D.carrier) : C = D := by
  cases C
  cases D
  cases h
  rfl
end QEC.Coding.LinearCode
