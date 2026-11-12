-- Prove2me | solution 1 for QEC.Distillation.HH18Postselection.postselectionInstrument_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:45:42.620695+00:00
-- url     : https://prove2.me/submissions/f63f9d1e-ce4e-431e-9404-811fbda9dc0a

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Postselection

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
theorem _root_.solution :
    postselectionInstrument.kraus.Complete :=
  jointStabilizerKrausFamily_complete
    (HH18PuncturedReedMuller.checkGenerator 0 1 4)
    (HH18PuncturedReedMuller.checkGenerator_commutes
      HH18NoisyInput.hh18_15_1_0_admissible)
end QEC.Distillation.HH18Postselection
