-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_DedekindBound_proof_53e4bf3d69ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:11:29.566549+00:00
-- url     : https://prove2.me/submissions/2f0f0748-da6e-46ed-b702-b553ee939470

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ZetaSevenHalves
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_dedekindZetaReal_le_pow_63af13c1180c
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_summable_dedekindZetaTerm_6d837e00dbf1
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_zetaSevenHalves_eq_tsum_288e87001abd
import Theorems.Thm_GroundTheory_Global_dedekindZeta_ofReal
import Theorems.Thm_GroundTheory_Global_one_le_dedekindZetaReal


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
namespace GroundTheory.Heights₂.Theta
namespace DedekindBound
theorem _root_.solution : ZetaSevenHalvesBounds.DedekindBound.Statement := by
  intro K _ _
  have h1 : (dedekindZeta K (7 / 2 : ℂ)).re = GroundTheory.Global.dedekindZetaReal K (7 / 2) := by
    have := GroundTheory.Global.dedekindZeta_ofReal K (s := 7 / 2) (by norm_num)
    push_cast at this
    rw [this, Complex.ofReal_re]
  have hle := ZetaSevenHalvesBounds.dedekindZetaReal_le_pow K (s := 7 / 2) (by norm_num)
  have hpos : 0 < GroundTheory.Global.dedekindZetaReal K (7 / 2) :=
    lt_of_lt_of_le one_pos (GroundTheory.Global.one_le_dedekindZetaReal
      (ZetaSevenHalvesBounds.summable_dedekindZetaTerm K (by norm_num)))
  rw [h1, ZetaSevenHalvesBounds.zetaSevenHalves_eq_tsum, ← Real.log_pow]
  exact Real.log_le_log hpos hle
end DedekindBound
end GroundTheory.Heights₂.Theta
