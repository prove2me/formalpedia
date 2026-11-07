-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:49:41.770267+00:00
-- url     : https://prove2.me/submissions/3ec953ff-a5e2-4d2a-97cf-8fa6b8645078

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
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) :
    (jointStabilizerInstrument checks hcomm).observe syndrome = syndrome :=
  rfl
end QEC.Coding.PauliSymplectic
