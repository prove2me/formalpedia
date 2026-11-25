-- Prove2me | solution 1 for PI.GalTorsConj.W.addLaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:31:34.648853+00:00
-- url     : https://prove2.me/submissions/21f913fb-ee22-48d8-bbd7-a5cc2f8c6727

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_hasDerivAt_wp
import Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_hasDerivAt_lam
import Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_wp_ne
import Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_ev_adm
import Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_stepA
import Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_stepB

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
open OriginCoordinatesAdd
namespace PI.GalTorsConj.W
theorem _root_.solution : AddLaw := by
  intro L z w hz hw hm hp
  have hB := stepB L hz hw hm hp
  refine ⟨hB, ?_⟩
  have hA := stepA L hz hw hm hp
  have hne := wp_ne L hz hw hm hp
  have hF : HasDerivAt (fun z' => L.weierstrassP (z' + w)) (L.derivWeierstrassP (z + w)) z :=
    HasDerivAt.comp_add_const z w (hasDerivAt_wp L hp)
  have hG := ((((hasDerivAt_lam L hz hne).pow 2).div_const 4).sub (hasDerivAt_wp L hz)).sub_const
    (L.weierstrassP w)
  have hEq : (fun z' => L.weierstrassP (z' + w)) =ᶠ[𝓝 z]
      (fun z' => lam L w z' ^ 2 / 4 - L.weierstrassP z' - L.weierstrassP w) := by
    filter_upwards [ev_adm L hz hm hp] with z' ⟨h1, h2, h3⟩
    rw [stepB L h1 hw h2 h3]
    rfl
  have hD := hF.unique (hG.congr_of_eventuallyEq hEq)
  rw [hD]
  unfold addY
  rw [← hB, hA]
  unfold lam
  norm_num
  ring
end PI.GalTorsConj.W
