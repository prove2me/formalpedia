-- Prove2me | solution 1 for QEC.Distillation.BK05T.fiveQubitWordWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-17T19:20:49.169564+00:00
-- url     : https://prove2.me/submissions/235e8009-1e02-4b50-a0a3-dd9f302d39dc

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection

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
namespace QEC.Distillation.BK05T
theorem _root_.solution
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (word : FiveQubitErrorWord) :
    0 ≤ fiveQubitWordWeight epsilon word := by
  unfold fiveQubitWordWeight
  exact Finset.prod_nonneg fun site _ =>
    tInputWeight_nonneg epsilon hzero hone (word site)
end QEC.Distillation.BK05T
