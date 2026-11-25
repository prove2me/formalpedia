-- Prove2me | solution 1 for PI.GalTorsConj.W.OriginCoordinatesAdd.stepA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:05:45.702999+00:00
-- url     : https://prove2.me/submissions/cd0142f9-aca0-476c-b80f-9122274dc289

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_hasDerivAt_lam
import Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_wp_ne
import Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_ev_adm
import Theorems.Thm_Formalism_L2_Th1_F_zetaAdd
import Theorems.Thm_Formalism_L2_Th1_F_zetaHasDeriv


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
open PI.GalTorsConj.W.OriginCoordinatesAdd
namespace PI.GalTorsConj.W.OriginCoordinatesAdd
theorem _root_.solution (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hm : z - w ∉ L.lattice) (hp : z + w ∉ L.lattice) :
    L.weierstrassP (z + w) = L.weierstrassP z -
      ((6 * L.weierstrassP z ^ 2 - L.g₂ / 2) * (L.weierstrassP z - L.weierstrassP w)
        - (L.derivWeierstrassP z - L.derivWeierstrassP w) * L.derivWeierstrassP z)
        / (L.weierstrassP z - L.weierstrassP w) ^ 2 / 2 := by
  have hne := wp_ne L hz hw hm hp
  have hF : HasDerivAt (fun z' => wZeta L (z' + w)) (-(L.weierstrassP (z + w))) z :=
    HasDerivAt.comp_add_const z w (zetaHasDeriv L (z + w) hp)
  have hG := ((zetaHasDeriv L z hz).add_const (wZeta L w)).add ((hasDerivAt_lam L hz hne).div_const 2)
  have hEq : (fun z' => wZeta L (z' + w)) =ᶠ[𝓝 z]
      (fun z' => wZeta L z' + wZeta L w + lam L w z' / 2) := by
    filter_upwards [ev_adm L hz hm hp] with z' ⟨h1, h2, h3⟩
    rw [zetaAdd L z' w h1 hw h3 h2, ← div_div]
    unfold lam
    ring
  have hD := hF.unique (hG.congr_of_eventuallyEq hEq)
  linear_combination -hD
end PI.GalTorsConj.W.OriginCoordinatesAdd
