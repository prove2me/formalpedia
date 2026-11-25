-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_LocAinf___eq_8b20937612a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:12:12.254436+00:00
-- url     : https://prove2.me/submissions/fc9ab80d-a486-41b4-88bc-b6d39564c04b

import Mathlib
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementPC
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions
open Loc NNReal
open Formalism.BasicNotions.LocAinf
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
namespace Formalism.BasicNotions.LocAinf
theorem _root_.solution : AI.μ = AI.π₁ * AI.ξ := by
  have h : (WittVector.teichmuller l AI.ε1) ^ l = WittVector.teichmuller l AI.ε := by
    rw [← map_pow, ε1, frobeniusEquiv_symm_pow_p]
  rw [μ, π₁, ξ, mul_comm, geom_sum_mul, h]
end Formalism.BasicNotions.LocAinf
