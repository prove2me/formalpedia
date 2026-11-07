-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:28:44.098039+00:00
-- url     : https://prove2.me/submissions/617f19dd-7d10-4efa-8cb9-0463275d81ca

import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Coding_Stabilizer_Measurement

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Semantics
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution (P : Binary ι) :
    (stabilizerInstrument P).kraus = stabilizerKrausFamily P :=
  rfl
end QEC.Coding.PauliSymplectic
