-- Prove2me | solution 1 for PI.RhsWLim.W.hermInv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:53.034627+00:00
-- url     : https://prove2.me/submissions/4a251b46-5157-4598-97d1-34638135f0bf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_UnimodS
import Theorems.Thm_PI_RhsWLim_W_gauge_ball
import Theorems.Thm_PI_RhsWLim_W_rmul_scale
import Theorems.Thm_PI_RhsWLim_W_one_of_sq
import Theorems.Thm_PI_RhsWLim_W_scale_mul_one
import Theorems.Thm_PI_RhsWLim_W_hb_sq
import Theorems.Thm_PI_RhsWLim_W_MB_Hb_conjT
import Theorems.Thm_PI_RhsWLim_W_MB_emb_conjT
import Theorems.Thm_PI_RhsWLim_W_MB_emb_mem_UWb
import Theorems.Thm_PI_RhsWLim_W_MB_emb_mul
import Theorems.Thm_PI_RhsWLim_W_MB_emb_one
import Theorems.Thm_PI_RhsWLim_W_rmulM_comp
import Theorems.Thm_PI_RhsWLim_W_rmulM_meas


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim HU
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (hU : UnitInv) : HermInv := by
  intro k r ν hk hG B₀ hB hBh
  have hHbh : (Hb k)ᴴ = Hb k := MB.Hb_conjT
  have hE : embWb k r (Hb k) ∈ UWb k r := MB.emb_mem_UWb (by rw [hHbh, hb_sq, Matrix.one_mul])
  have hEu : (embWb k r (Hb k))ᴴ * embWb k r (Hb k) = 1 := by
    rw [MB.emb_conjT, hHbh, ← MB.emb_mul, hb_sq, MB.emb_one]
  have hBm : embWb k r B₀ ∈ UWb k r := MB.emb_mem_UWb hB
  have hinv : embWb k r B₀ * (embWb k r (Hb k) * embWb k r B₀ * embWb k r (Hb k)) = 1 := by
    rw [← MB.emb_mul, ← MB.emb_mul, ← MB.emb_mul]
    have : B₀ * (Hb k * B₀ * Hb k) = 1 := by
      calc B₀ * (Hb k * B₀ * Hb k) = (B₀ᴴ * Hb k * B₀) * Hb k := by rw [hBh]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hB, hb_sq]
    rw [this, MB.emb_one]
  have hEinv := hU k r ν hk hG _ hE hEu
  obtain ⟨ρ, h0, ht⟩ := gauge_ball ν hG
  have hsc := rmul_scale ν hG.1 _ hBm _ h0.ne' ht.ne
  set c := ν.map (rmulM (embWb k r B₀)) (bBall k r ρ) / ν (bBall k r ρ) with hc
  have h2 : ν.map (rmulM (embWb k r (Hb k) * embWb k r B₀ * embWb k r (Hb k))) = c • ν := by
    rw [← rmulM_comp, ← rmulM_comp, ← Measure.map_map (rmulM_meas _) ((rmulM_meas _).comp (rmulM_meas _)),
      ← Measure.map_map (rmulM_meas _) (rmulM_meas _), hEinv, hsc, Measure.map_smul, hEinv]
  have hcc := scale_mul_one ν _ _ hinv _ h0.ne' ht.ne c c hsc h2
  rw [hsc, one_of_sq c hcc, one_smul]
end PI.RhsWLim.W
