-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_dedekindZetaReal_le_pow_63af13c1180c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:12.500147+00:00
-- url     : https://prove2.me/submissions/28024785-8548-4dac-ae63-4639a0a4066c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ZetaSevenHalves
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_sum_rpow_neg_le_pow_add2b3ef4a0c
import Theorems.Thm_GroundTheory_Global_dedekindZetaTerm_nonneg
import Theorems.Thm_GroundTheory_Global_sum_range_dedekindZetaTerm


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
open NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid
noncomputable section
open GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)
namespace GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
theorem _root_.solution {s : ℝ} (hs : 1 < s) :
    GroundTheory.Global.dedekindZetaReal K s ≤ (∑' m : ℕ, (m : ℝ) ^ (-s)) ^ Module.finrank ℚ K := by
  refine Real.tsum_le_of_sum_range_le (fun n => GroundTheory.Global.dedekindZetaTerm_nonneg K s n)
    fun N => ?_
  rw [GroundTheory.Global.sum_range_dedekindZetaTerm]
  exact sum_rpow_neg_le_pow K _ hs
end GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
