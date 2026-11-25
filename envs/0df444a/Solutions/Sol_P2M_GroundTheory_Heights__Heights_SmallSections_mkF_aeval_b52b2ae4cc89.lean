-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SmallSections_mkF_aeval_b52b2ae4cc89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:17:03.533923+00:00
-- url     : https://prove2.me/submissions/031c3c48-95a7-4e29-af2a-ddb958e5fc2b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.SmallSections
theorem _root_.solution (P : ArithVariety n) {σ : Type*} (g : σ → MvPolynomial (Coord n) ℤ)
    (F : MvPolynomial σ ℤ) : P.mkF (aeval g F) = aeval (fun j ↦ P.mkF (g j)) F := by
  rw [aeval_def, aeval_def, eval₂_comp_left]
  congr 1
end GroundTheory.Heights₂.Heights.SmallSections
