-- Prove2me | solution 1 for PI.GalTorsConj.W.ZetaDoubling.hasDerivAt_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:40.869147+00:00
-- url     : https://prove2.me/submissions/c22c59a7-a822-47ab-a451-ae2b36ee4080

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Theorems.Thm_Formalism_L2_Th1_F_pSecond
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
open PI.GalTorsConj.W.ZetaDoubling
open OriginCoordinatesAdd
namespace PI.GalTorsConj.W.ZetaDoubling
theorem _root_.solution (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) (hy : L.derivWeierstrassP z ≠ 0) :
    HasDerivAt (mu L)
      ((12 * L.weierstrassP z * L.derivWeierstrassP z * L.derivWeierstrassP z
        - (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) * (6 * L.weierstrassP z ^ 2 - L.g₂ / 2))
        / L.derivWeierstrassP z ^ 2) z := by
  have hN := (((hasDerivAt_wp L hz).pow 2).const_mul (6 : ℂ)).sub_const (L.g₂ / 2)
  have hQ := hN.div (pSecond L z hz) hy
  refine (hQ.congr_of_eventuallyEq (f₁ := mu L)
    (Filter.Eventually.of_forall (fun y => rfl))).congr_deriv ?_
  simp only [Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  ring
end PI.GalTorsConj.W.ZetaDoubling
