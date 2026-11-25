-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rorth_inK_of_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:27.057201+00:00
-- url     : https://prove2.me/submissions/f82510cc-6679-47c5-b268-20e84b2efbea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RorthFunctionalEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (h1 : Zᴴ = -Z)
    (h2 : Z * Jm ε = Jm ε * Z) : inK ε Z := by
  refine ⟨?_, h2⟩
  unfold inG
  rw [h1, Matrix.neg_mul, h2, neg_add_cancel]
end ReciprocityTheory.ChartRestriction.DS
