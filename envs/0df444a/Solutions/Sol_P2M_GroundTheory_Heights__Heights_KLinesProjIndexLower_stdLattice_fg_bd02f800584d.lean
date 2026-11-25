-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesProjIndexLower_stdLattice_fg_bd02f800584d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:00:57.981064+00:00
-- url     : https://prove2.me/submissions/b10d3d85-e7b5-490b-be47-955a7d9984b4

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
    ((stdLattice K k).restrictScalars ℤ).FG :=
  (Submodule.fg_span (Set.finite_range _)).restrictScalars
end GroundTheory.Heights₂.Heights.KLinesProjIndexLower
