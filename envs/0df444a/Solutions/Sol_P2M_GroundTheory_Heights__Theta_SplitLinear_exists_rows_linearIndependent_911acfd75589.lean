-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SplitLinear_exists_rows_linearIndependent_911acfd75589
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:41.208112+00:00
-- url     : https://prove2.me/submissions/755af141-018a-40b9-a865-fd2c31f79051

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qm10_exists_rows_linearIndependent__b388476fc269
import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRowsLinearIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_SplitLinear_RankMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.SplitLinear
open Matrix Module
universe u
variable {K : Type*} [Field K]
namespace GroundTheory.Heights₂.Theta.SplitLinear
theorem _root_.solution {r : Type u} {c : Type*} [Fintype r] [Fintype c]
    (P : Matrix r c K) {k : ℕ}
    (hk : k ≤ P.rank) : ∃ I : Fin k → r, LinearIndependent K (fun p => P (I p)) :=
  _root_.P2M_UpperTheory_Reformulated_B_Qm10_exists_rows_linearIndependent__b388476fc269 P hk
end GroundTheory.Heights₂.Theta.SplitLinear
