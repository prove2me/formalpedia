-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:49:52.858308+00:00
-- url     : https://prove2.me/submissions/2de38b42-8fc7-4502-8b24-d6bba6dd8b3f

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right)) :
    (jointStabilizerInstrument checks hcomm).kraus =
      jointStabilizerKrausFamily checks hcomm :=
  rfl
end QEC.Coding.PauliSymplectic
