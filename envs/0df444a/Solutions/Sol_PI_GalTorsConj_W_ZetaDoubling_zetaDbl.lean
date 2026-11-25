-- Prove2me | solution 1 for PI.GalTorsConj.W.ZetaDoubling.zetaDbl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:53.910102+00:00
-- url     : https://prove2.me/submissions/1c9a0aa4-8295-44ea-b33b-953494e8c24e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_hasDerivAt_two_mul
import Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_ev_self
import Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_derivWeierstrassP_ne_zero
import Theorems.Thm_Formalism_L2_Th1_F_pSecond
import Theorems.Thm_Formalism_L2_Th1_F_sigmaDouble
import Theorems.Thm_Formalism_L2_Th1_F_sigmaLogDeriv
import Theorems.Thm_Formalism_L2_Th1_F_sigmaZero


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
open PI.GalTorsConj.W.ZetaDoubling
open OriginCoordinatesAdd
namespace PI.GalTorsConj.W.ZetaDoubling
theorem _root_.solution (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∉ L.lattice) :
    wZeta L (2 * z) = 2 * wZeta L z + mu L z / 2 := by
  have hy := derivWeierstrassP_ne_zero L hz h2
  have hs : wSigma L z ≠ 0 := fun h => hz ((sigmaZero L z).1 h)
  have hF := (sigmaLogDeriv L (2 * z) h2).comp z (hasDerivAt_two_mul z)
  have hG := (pSecond L z hz).neg.mul ((sigmaLogDeriv L z hz).pow 4)
  have heq : (fun y => -L.derivWeierstrassP y * wSigma L y ^ 4) =ᶠ[𝓝 z]
      (wSigma L ∘ fun y : ℂ => 2 * y) := by
    filter_upwards [ev_self L hz] with y hy'
    exact (sigmaDouble L y hy').symm
  have e := (hF.congr_of_eventuallyEq heq).unique hG
  rw [sigmaDouble L z hz] at e
  simp only [Pi.pow_apply, Pi.neg_apply, Nat.cast_ofNat, show (4 : ℕ) - 1 = 3 from rfl] at e
  have e2 : wZeta L (2 * z) * (-L.derivWeierstrassP z) * 2 =
      -(6 * L.weierstrassP z ^ 2 - L.g₂ / 2) + -L.derivWeierstrassP z * (4 * wZeta L z) := by
    apply mul_right_cancel₀ (pow_ne_zero 4 hs)
    linear_combination e
  have hy2 : (2 : ℂ) * L.derivWeierstrassP z ≠ 0 := mul_ne_zero two_ne_zero hy
  have e3 : wZeta L (2 * z) = (6 * L.weierstrassP z ^ 2 - L.g₂ / 2 +
      4 * L.derivWeierstrassP z * wZeta L z) / (2 * L.derivWeierstrassP z) := by
    rw [eq_div_iff hy2]
    linear_combination -e2
  rw [e3]
  unfold mu
  field_simp
  ring
end PI.GalTorsConj.W.ZetaDoubling
