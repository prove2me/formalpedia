-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.CB.hpk_conjT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:32:45.434051+00:00
-- url     : https://prove2.me/submissions/e10204be-adc0-43ad-8a52-7ca4031ff477

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiIntH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TLeftH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiRNonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_hpk_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_sgn_sig
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_star_sgn


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
theorem _root_.solution : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  simp only [conjTranspose_apply, hpk_apply]
  by_cases h : j = sigI k r i
  · subst h; rw [if_pos (sig_sig i).symm, if_pos rfl, sgn_sig, star_sgn]
  · have h' : ¬ i = sigI k r j := fun h2 => h (by rw [h2, sig_sig])
    rw [if_neg h', if_neg h, star_zero]
end ReciprocityTheory.ChartRestriction.DS.Xi.CB
