-- Prove2me | solution 1 for PI.GalTorsConj.W.dblLaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:02:37.215513+00:00
-- url     : https://prove2.me/submissions/d7fd9416-4a0a-4075-a435-80d7e5dd7fc0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_hasDerivAt_two_mul
import Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_ev_two
import Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_ev_self
import Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_derivWeierstrassP_ne_zero
import Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_hasDerivAt_mu
import Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_dbl_alg
import Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_dblB
import Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_hasDerivAt_wp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Formalism.L2.Th1.F
open Filter Topology
open OriginCoordinatesAdd ZetaDoubling
namespace PI.GalTorsConj.W
theorem _root_.solution : DblLaw := by
  intro L z hz h2
  refine ⟨dblB L hz h2, ?_⟩
  have hy := derivWeierstrassP_ne_zero L hz h2
  have hL := (hasDerivAt_wp L h2).comp z (hasDerivAt_two_mul z)
  have hR := (((hasDerivAt_mu L hz hy).pow 2).div_const (4 : ℂ)).sub
    ((hasDerivAt_wp L hz).const_mul (2 : ℂ))
  have heq : (fun y => mu L y ^ 2 / 4 - 2 * L.weierstrassP y) =ᶠ[𝓝 z]
      (L.weierstrassP ∘ fun y : ℂ => 2 * y) := by
    filter_upwards [ev_self L hz, ev_two L h2] with y h1 h3
    show mu L y ^ 2 / 4 - 2 * L.weierstrassP y = L.weierstrassP (2 * y)
    rw [dblB L h1 h3]
    rfl
  have e := (hL.congr_of_eventuallyEq heq).unique hR
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at e
  unfold mu at e
  unfold dblY
  rw [← dbl_alg _ _ _ hy]
  linear_combination (1 / 2 : ℂ) * e
end PI.GalTorsConj.W
