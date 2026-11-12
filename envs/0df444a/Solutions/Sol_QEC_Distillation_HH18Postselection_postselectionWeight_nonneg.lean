-- Prove2me | solution 1 for QEC.Distillation.HH18Postselection.postselectionWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:28:44.130199+00:00
-- url     : https://prove2.me/submissions/b0dcaa9b-d0fe-4530-8d6b-fc418f60f64f

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Postselection
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Postselection
open Coding Semantics
open Coding.PauliSymplectic
open HH18SyndromeDecoding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.HH18Postselection
theorem _root_.solution (outcome : DistillationOutcome)
    (rho : DensityOperator PhysicalRegister) :
    0 ≤ postselectionWeight outcome rho :=
  postselectionInstrument.bornWeight_nonneg outcome rho
end QEC.Distillation.HH18Postselection
