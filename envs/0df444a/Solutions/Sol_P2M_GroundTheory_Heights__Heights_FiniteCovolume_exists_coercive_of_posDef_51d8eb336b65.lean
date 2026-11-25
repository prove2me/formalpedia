-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_coercive_of_posDef_51d8eb336b65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:32:40.946052+00:00
-- url     : https://prove2.me/submissions/b0f2c012-9276-4eed-9527-7a75cee1a10d

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_CoerciveOfPositiveDefinite_exists_coercive_of_posDef__05ec9a5f4d38
import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Imports
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CoerciveOfPositiveDefinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLatticePointsBelowFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {ι : Type*} [Fintype ι] {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ (z : ι → ℂ) (j : ι), c * ‖z j‖ ^ 2 ≤ (star z ⬝ᵥ (P *ᵥ z)).re :=
  _root_.P2M_UpperTheory_Reformulated_B_CoerciveOfPositiveDefinite_exists_coercive_of_posDef__05ec9a5f4d38 hP
end GroundTheory.Heights₂.Heights.FiniteCovolume
