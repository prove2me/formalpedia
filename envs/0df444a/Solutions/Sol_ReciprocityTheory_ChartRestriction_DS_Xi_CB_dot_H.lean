-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.CB.dot_H
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:36:17.169107+00:00
-- url     : https://prove2.me/submissions/362df24c-39a0-480f-980d-7a39cc613bf8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiIntH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TLeftH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiRNonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_HE_HE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_HE_adj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_HE_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.CB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS
variable {k r : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.CB
theorem _root_.solution (v w : Fin (2 * r + k + 1) → ℂ) :
    star (Hpk k r *ᵥ v) ⬝ᵥ (Hpk k r *ᵥ w) = star v ⬝ᵥ w := by
  have h := HE_adj (HE k r (WithLp.toLp 2 v)) (WithLp.toLp 2 w)
  rw [HE_HE] at h
  simp only [HE_apply, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp] at h
  rw [dotProduct_comm (star (Hpk k r *ᵥ v)), ← h, dotProduct_comm]
end ReciprocityTheory.ChartRestriction.DS.Xi.CB
