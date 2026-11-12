-- Prove2me | solution 2 for QEC.Distillation.HH18Parameterized.noisyResources_at_site
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:37:36.855212+00:00
-- url     : https://prove2.me/submissions/eab40d27-b6ff-4f5d-a23d-a44e978971ca

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (site : PhysicalSite m w) :
    noisyResources m w epsilon (resourceSiteEquiv m w site) =
      HH18NoisyInput.noisyTInvResource epsilon :=
  rfl
end QEC.Distillation.HH18Parameterized
