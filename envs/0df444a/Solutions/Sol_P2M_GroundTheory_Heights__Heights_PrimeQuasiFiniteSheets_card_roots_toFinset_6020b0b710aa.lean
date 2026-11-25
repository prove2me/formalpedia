-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_card_roots_toFinset_6020b0b710aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:27.622532+00:00
-- url     : https://prove2.me/submissions/8797cd25-563c-4b26-bb0f-c2b973f5cb5e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFiniteFibresDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSimpleRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPrimeQuasiFiniteSheets

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
open MvPolynomial
open GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
theorem _root_.solution {p : Polynomial ℂ} (hp : p.Separable) : p.roots.toFinset.card = p.natDegree := by
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hp), IsAlgClosed.card_roots_eq_natDegree]
end GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
