-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.ModW.modF_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:11:58.096812+00:00
-- url     : https://prove2.me/submissions/8dd71390-4405-48ab-96b8-1e7239f99087

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
theorem _root_.solution (V : Set (MG G hG)) (hV : IsCompact V) :
    ∃ M : ℝ, ∀ v ∈ V, (Measure.modularCharacterFun v : ℝ) ≤ M := by
  have K : TopologicalSpace.PositiveCompacts (MG G hG) := Classical.arbitrary _
  set C : Set (MG G hG) :=
    (fun p : MG G hG × MG G hG => p.1 * p.2⁻¹) '' ((K : Set (MG G hG)) ×ˢ V) with hCdef
  have hC : IsCompact C := (K.isCompact.prod hV).image (continuous_fst.mul continuous_snd.inv)
  have hK0 : 0 < (Measure.haar : Measure (MG G hG)) K :=
    Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty
  have hKt : (Measure.haar : Measure (MG G hG)) K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hCt : (Measure.haar : Measure (MG G hG)) C ≠ ⊤ := hC.measure_lt_top.ne
  refine ⟨((Measure.haar : Measure (MG G hG)) C / (Measure.haar : Measure (MG G hG)) K).toReal,
    fun v hv => ?_⟩
  have h := (MeasurableEquiv.mulRight v).map_apply (μ := (Measure.haar : Measure (MG G hG)))
    (K : Set (MG G hG))
  rw [MeasurableEquiv.coe_mulRight, map_mul_right_haar v, Measure.smul_apply, ENNReal.smul_def] at h
  have hsub : (fun x => x * v) ⁻¹' (K : Set (MG G hG)) ⊆ C := by
    intro x hx
    exact ⟨(x * v, v), ⟨hx, hv⟩, by simp⟩
  have hle : (Measure.modularCharacterFun v : ℝ≥0∞) * (Measure.haar : Measure (MG G hG)) K
      ≤ (Measure.haar : Measure (MG G hG)) C := by
    rw [← smul_eq_mul, h]
    exact measure_mono hsub
  have hle' : (Measure.modularCharacterFun v : ℝ≥0∞)
      ≤ (Measure.haar : Measure (MG G hG)) C / (Measure.haar : Measure (MG G hG)) K :=
    (ENNReal.le_div_iff_mul_le (Or.inl hK0.ne') (Or.inl hKt)).2 hle
  rw [← ENNReal.coe_toReal]
  exact ENNReal.toReal_mono (ENNReal.div_ne_top hCt hK0.ne') hle'
end PI.QuotSetU.UnitaryGroupMassFormula.ModW
