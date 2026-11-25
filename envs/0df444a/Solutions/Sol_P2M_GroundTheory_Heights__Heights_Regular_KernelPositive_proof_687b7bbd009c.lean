-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_proof_687b7bbd009c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:25:13.14526+00:00
-- url     : https://prove2.me/submissions/d4680182-c7ae-4b57-8862-729d076b9fe6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PKernelPositive
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_kernelPositive_statement_8f11d8dd3f47

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace KernelPositive
theorem _root_.solution (_h0 : Tau0Holomorphic.Statement) : KernelPositive.Statement :=
  kernelPositive_statement
end KernelPositive
end GroundTheory.Heights₂.Heights.Regular
