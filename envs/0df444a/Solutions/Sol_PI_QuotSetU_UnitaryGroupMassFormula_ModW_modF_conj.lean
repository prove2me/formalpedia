-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.ModW.modF_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:04.07722+00:00
-- url     : https://prove2.me/submissions/48bc98f2-88f1-40de-92af-fbdbd45796ca

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModCore
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_map_mul_right_haar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.ModW
open PI MG
variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
namespace PI.QuotSetU.UnitaryGroupMassFormula.ModW
theorem _root_.solution (φ : MG G hG ≃ₜ* MG G hG) (g : MG G hG) :
    Measure.modularCharacterFun (φ g) = Measure.modularCharacterFun g := by
  rw [Measure.modularCharacterFun_eq_haarScalarFactor
    (Measure.map φ (Measure.haar : Measure (MG G hG))) (φ g)]
  have hφ : Measurable φ := φ.continuous.measurable
  have e1 : Measure.map (· * φ g) (Measure.map φ (Measure.haar : Measure (MG G hG)))
      = Measure.modularCharacterFun g • Measure.map φ (Measure.haar : Measure (MG G hG)) := by
    rw [Measure.map_map (measurable_mul_const (φ g)) hφ]
    have e : ((· * φ g) ∘ ⇑φ) = (⇑φ ∘ (· * g)) := by
      funext x
      simp [map_mul]
    rw [e, ← Measure.map_map hφ (measurable_mul_const g), map_mul_right_haar g, Measure.map_smul]
  simp only [e1, Measure.haarScalarFactor_smul, Measure.haarScalarFactor_self, smul_eq_mul, mul_one]
end PI.QuotSetU.UnitaryGroupMassFormula.ModW
