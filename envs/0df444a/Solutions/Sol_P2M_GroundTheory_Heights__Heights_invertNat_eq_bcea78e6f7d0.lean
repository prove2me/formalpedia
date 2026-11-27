-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_invertNat_eq_bcea78e6f7d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:09:36.422613+00:00
-- url     : https://prove2.me/submissions/c6a0fbad-bae5-408c-ba21-9105608f5f3b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (m : ℕ) (A : Subalgebra ℤ Ω) :
    invertNat m A.toSubring = (IndefiniteRowSideFullHecke.Antisym.invertNat A m).toSubring := by
  rw [IndefiniteRowSideFullHecke.Antisym.invertNat, Algebra.adjoin_int]
  rfl
end GroundTheory.Heights₂.Heights
