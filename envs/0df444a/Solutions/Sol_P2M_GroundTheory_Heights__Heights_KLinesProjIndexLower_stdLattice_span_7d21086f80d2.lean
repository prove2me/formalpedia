-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesProjIndexLower_stdLattice_span_7d21086f80d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:01:08.577609+00:00
-- url     : https://prove2.me/submissions/e55f3723-51bc-480b-be00-721f6d6f41ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesProjIndexLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.KLinesProjIndexLower
namespace GroundTheory.Heights₂.Heights.KLinesProjIndexLower
theorem _root_.solution (K : Type) [Field K] [NumberField K] (k : ℕ) :
    Submodule.span K ((stdLattice K k : Submodule (𝓞 K) (Fin k → K)) : Set (Fin k → K)) = ⊤ :=
  (HermLattice.standard K k).span_eq
end GroundTheory.Heights₂.Heights.KLinesProjIndexLower
