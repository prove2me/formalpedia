-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_of_le_fg_fd0431823b0a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:22:07.69318+00:00
-- url     : https://prove2.me/submissions/3e6d5bc4-67c2-46da-8cf8-80bf3d633270

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
universe u
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {H K : AddSubgroup A} (hHK : H ≤ K) (hK : K.FG) : H.FG := by
  have hK' : K.toIntSubmodule.FG := (Submodule.fg_iff_addSubgroup_fg _).2 hK
  have := isNoetherian_of_fg_of_noetherian _ hK'
  exact (Submodule.fg_iff_addSubgroup_fg H.toIntSubmodule).1
    (Submodule.FG.of_le_of_isNoetherian (S := H.toIntSubmodule) (T := K.toIntSubmodule) hHK)
end GroundTheory.Heights₂.Heights.FiniteCovolume
