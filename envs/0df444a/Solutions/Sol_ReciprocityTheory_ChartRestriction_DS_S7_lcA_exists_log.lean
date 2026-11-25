-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.lcA_exists_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:31:13.786921+00:00
-- url     : https://prove2.me/submissions/eeed14d7-d910-4dd3-a91f-a89f4058b27a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LocalA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_exists_local_matrix_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ (∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (ℓ k) = k) ∧
      (∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ℓ (NormedSpace.exp Y) = Y) := by
  first
  | exact exists_local_matrix_log
  | exact exists_local_matrix_log (n := n)
end ReciprocityTheory.ChartRestriction.DS.S7
