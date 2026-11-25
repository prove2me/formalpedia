-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_zetaSevenHalves_eq_tsum_288e87001abd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:18.449099+00:00
-- url     : https://prove2.me/submissions/e9dbbd28-14bc-47cb-82ac-ffbdd14561c4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ZetaSevenHalves
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm

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
namespace GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
theorem _root_.solution :
    zetaSevenHalves = ∑' m : ℕ, (m : ℝ) ^ (-(7 / 2 : ℝ)) := by
  have h := zeta_eq_tsum_one_div_nat_cpow (s := (7 / 2 : ℂ)) (by norm_num)
  have h2 : (∑' n : ℕ, 1 / (n : ℂ) ^ (7 / 2 : ℂ)) =
      ((∑' m : ℕ, (m : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1
    ext n
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.cpow_neg, one_div]
    push_cast
    rfl
  rw [zetaSevenHalves, h, h2, Complex.ofReal_re]
end GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
