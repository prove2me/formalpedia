-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.ModW.map_onG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:22:23.943324+00:00
-- url     : https://prove2.me/submissions/dff1cbd9-7c62-4f1d-9c4b-8b2b1c3c14a5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_measEmb

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
theorem _root_.solution (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) : (onG hG μ).map val = μ := by
  rw [onG, measEmb.map_comap]
  have hr : Set.range (val : MG G hG → MtM m) = {x | Matrix.of x ∈ G} := Subtype.range_coe
  rw [hr]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  simpa using hμ.2.2.1
end PI.QuotSetU.UnitaryGroupMassFormula.ModW
