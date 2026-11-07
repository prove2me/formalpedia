-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.jointStabilizerProjector_mul_of_ne_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:36:42.760386+00:00
-- url     : https://prove2.me/submissions/7f49b60e-1a31-41ac-b9f9-62aa8587bf20

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_mul_of_ne

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
    (syndromeLeft syndromeRight : JointSyndrome κ) (hne : syndromeLeft ≠ syndromeRight) :
    jointStabilizerProjector checks hcomm syndromeRight *
      jointStabilizerProjector checks hcomm syndromeLeft = 0 :=
  jointStabilizerProjector_mul_of_ne checks hcomm syndromeRight syndromeLeft hne.symm
end QEC.Coding.PauliSymplectic
