-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.sum_lev_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:19:12.826832+00:00
-- url     : https://prove2.me/submissions/0b787c63-7045-420a-aa6a-9b0f524d1936

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_levPos_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
theorem _root_.solution (F : Fin (2 * (1 + r') + k + 1) → ℝ) (hF : ∀ q, 0 ≤ F q) :
    ∑ j : Fin (2 * r' + k + 1), F (levPos k 1 r' j) ≤ ∑ q, F q := by
  have e := Finset.sum_map Finset.univ ⟨levPos k 1 r', levPos_inj k r'⟩ F
  simp only [Function.Embedding.coeFn_mk] at e
  rw [← e]
  exact Finset.sum_le_univ_sum_of_nonneg hF
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
