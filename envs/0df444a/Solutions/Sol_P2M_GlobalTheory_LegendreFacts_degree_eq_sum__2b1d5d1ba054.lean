-- Prove2me | solution 1 for P2M_GlobalTheory_LegendreFacts_degree_eq_sum__2b1d5d1ba054
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:39:59.488439+00:00
-- url     : https://prove2.me/submissions/a17114c6-b2f0-4686-b055-6b86bfaee571

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open GlobalTheory GlobalTheory.LegendreFacts
open GlobalTheory.LegendreBounds
namespace GlobalTheory.LegendreFacts
theorem _root_.solution {σ : Type} [Fintype σ] (A : σ →₀ ℕ) : A.degree = ∑ j, A j := by
  rw [Finsupp.degree_apply]
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro j _ hj
  simpa using hj
end GlobalTheory.LegendreFacts
