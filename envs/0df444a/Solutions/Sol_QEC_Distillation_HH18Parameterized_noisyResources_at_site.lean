-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.noisyResources_at_site
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T18:42:57.00919+00:00
-- url     : https://prove2.me/submissions/0bc8a168-fbec-40de-b43c-69094fdbe694

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

theorem solution (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (site : PhysicalSite m w) :
    noisyResources m w epsilon (resourceSiteEquiv m w site) =
      HH18NoisyInput.noisyTInvResource epsilon := rfl