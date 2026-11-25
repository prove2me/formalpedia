-- Prove2me | solution 1 for PI.GalTorsConj.W.OriginCoordinatesAdd.ev_adm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:47:41.13832+00:00
-- url     : https://prove2.me/submissions/a6f9f969-f1e7-4479-a552-a4e02acb7312

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_ev_notMem

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
theorem _root_.solution (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice) (hm : z - w ∉ L.lattice)
    (hp : z + w ∉ L.lattice) :
    ∀ᶠ z' in 𝓝 z, z' ∉ L.lattice ∧ z' - w ∉ L.lattice ∧ z' + w ∉ L.lattice := by
  have h1 := ev_notMem L (f := fun z' => z') continuousAt_id hz
  have h2 := ev_notMem L (f := fun z' => z' - w) (continuousAt_id.sub continuousAt_const) hm
  have h3 := ev_notMem L (f := fun z' => z' + w) (continuousAt_id.add continuousAt_const) hp
  filter_upwards [h1, h2, h3] with z' a b c using ⟨a, b, c⟩
end PI.GalTorsConj.W.OriginCoordinatesAdd
