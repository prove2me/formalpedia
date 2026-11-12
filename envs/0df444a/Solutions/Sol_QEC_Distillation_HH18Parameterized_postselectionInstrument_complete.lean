-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.postselectionInstrument_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:38:50.421755+00:00
-- url     : https://prove2.me/submissions/d6896bb2-7aad-4808-a8cd-77d8bff099c5

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Postselection
import Theorems.Thm_QEC_Distillation_HH18Parameterized_fullSyndromeInstrument_complete


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
theorem _root_.solution {w r m : Nat} (h : Admissible w r m) :
    (postselectionInstrument h).kraus.Complete :=
  fullSyndromeInstrument_complete h
end QEC.Distillation.HH18Parameterized
