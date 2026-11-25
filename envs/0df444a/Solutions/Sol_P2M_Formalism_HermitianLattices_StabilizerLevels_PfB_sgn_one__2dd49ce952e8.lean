-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_StabilizerLevels_PfB_sgn_one__2dd49ce952e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:27.5292+00:00
-- url     : https://prove2.me/submissions/0f0f87d3-3286-42ef-901d-1d922e1161b7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IntermediateField
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution {L : Type*} [Field L] [Algebra ℚ L] {τ : Gal(L/ℚ)} {x : L} (h : sgn τ x = 1) :
    τ x = x := by
  unfold sgn at h
  by_contra hne
  rw [if_neg hne] at h
  exact absurd h (by decide)
end Formalism.HermitianLattices.StabilizerLevels.PfB
