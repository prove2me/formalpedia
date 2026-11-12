-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.postselectionWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:36:24.368386+00:00
-- url     : https://prove2.me/submissions/0b98de91-a5ef-4bb1-9610-578133ca3771

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Postselection
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat} (h : Admissible w r m)
    (outcome : DistillationOutcome) (rho : DensityOperator (PhysicalRegister m w)) :
    0 ≤ postselectionWeight h outcome rho :=
  (postselectionInstrument h).bornWeight_nonneg outcome rho
end QEC.Distillation.HH18Parameterized
