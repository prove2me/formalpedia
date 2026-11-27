-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.ModW.onG_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:15:13.73339+00:00
-- url     : https://prove2.me/submissions/b7e19121-771f-495b-a249-b5bb220727fe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_measEmb
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_continuous_lmulQ
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_map_onG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.ModW
open PI
variable {m : ℕ}
variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
open MG
namespace PI.QuotSetU.UnitaryGroupMassFormula.ModW
theorem _root_.solution (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) : Measure.IsMulLeftInvariant (onG hG μ) := by
  refine ⟨fun g => ?_⟩
  have hcomp : (val ∘ (fun x : MG G hG => g * x)) = lmulQ g.toM ∘ val := funext fun x => rfl
  have hmeasL : Measurable (lmulQ (m := m) g.toM) := (continuous_lmulQ _).measurable
  have hmul : Measurable (fun x : MG G hG => g * x) :=
    (measEmb (hG := hG)).measurable_comp_iff.1 (by rw [hcomp]; exact hmeasL.comp measEmb.measurable)
  calc Measure.map (fun x => g * x) (onG hG μ)
      = Measure.comap val (Measure.map val (Measure.map (fun x => g * x) (onG hG μ))) :=
        (measEmb.comap_map _).symm
    _ = Measure.comap val (Measure.map (lmulQ g.toM) (Measure.map val (onG hG μ))) := by
        rw [Measure.map_map measEmb.measurable hmul, hcomp, ← Measure.map_map hmeasL measEmb.measurable]
    _ = Measure.comap val μ := by rw [map_onG μ hμ, hμ.2.2.2 _ g.toM_mem]
    _ = onG hG μ := rfl
end PI.QuotSetU.UnitaryGroupMassFormula.ModW
