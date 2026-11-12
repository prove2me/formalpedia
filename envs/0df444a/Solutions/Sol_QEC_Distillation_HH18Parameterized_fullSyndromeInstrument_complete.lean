-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.fullSyndromeInstrument_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:36:09.849194+00:00
-- url     : https://prove2.me/submissions/ecf5e7db-db53-425d-bb26-694a0a1debcd

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome

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
    (fullSyndromeInstrument h).kraus.Complete :=
  jointStabilizerKrausFamily_complete
    (HH18PuncturedReedMuller.checkGenerator w r m)
    (HH18PuncturedReedMuller.checkGenerator_commutes h)
end QEC.Distillation.HH18Parameterized
