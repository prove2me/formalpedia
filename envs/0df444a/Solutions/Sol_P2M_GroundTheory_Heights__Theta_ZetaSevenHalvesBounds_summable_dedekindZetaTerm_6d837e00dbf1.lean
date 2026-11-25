-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_summable_dedekindZetaTerm_6d837e00dbf1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:30.468004+00:00
-- url     : https://prove2.me/submissions/44192754-a135-4233-a98d-7f95047f8c58

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
    Summable (GroundTheory.Global.dedekindZetaTerm K s) := by
  refine summable_of_sum_range_le (c := (∑' m : ℕ, (m : ℝ) ^ (-s)) ^ Module.finrank ℚ K) (fun n => GroundTheory.Global.dedekindZetaTerm_nonneg K s n)
    fun N => ?_
  rw [GroundTheory.Global.sum_range_dedekindZetaTerm]
  exact sum_rpow_neg_le_pow K _ hs
end GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
