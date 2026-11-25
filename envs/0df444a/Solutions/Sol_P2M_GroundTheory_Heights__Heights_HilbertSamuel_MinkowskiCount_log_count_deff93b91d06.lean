-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_log_count_deff93b91d06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:30:38.120106+00:00
-- url     : https://prove2.me/submissions/caadb661-6222-447e-bb57-0afc5c375c58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMinkowskiCount
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_finite_latticePoints_4885546fbfad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_unitBallVolume_pos_8f4cd9dcd1b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_volume_ball_one_76ffe3d83cf1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_volume_ball_half_le_51476678b1c0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Module Metric
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount
theorem _root_.solution (La : Submodule ℤ V) [DiscreteTopology La] [IsZLattice ℝ La] (ρ : ℝ)
    (hρ : 0 < ρ) :
    Real.log (unitBallVolume (finrank ℝ V)) + (finrank ℝ V : ℝ) * Real.log (ρ / 2) -
        Real.log (ZLattice.covolume La) ≤
      Real.log ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := by
  set b := Module.Free.chooseBasis ℤ La
  have fund := ZLattice.isAddFundamentalDomain b (volume : Measure V)
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain La volume fund
  have hFtop : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hle := volume_ball_half_le La ρ fund
  rw [Measure.addHaar_ball_of_pos volume 0 (half_pos hρ), volume_ball_one] at hle
  have hle' := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFtop) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (unitBallVolume_pos _).le, ENNReal.toReal_natCast, ← measureReal_def,
    ← hcov] at hle'
  have hcpos := ZLattice.covolume_pos La volume
  have hN : 0 < ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := by
    have : 0 < {x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard :=
      (Set.ncard_pos (finite_latticePoints La ρ)).mpr ⟨0, La.zero_mem, by simp [hρ.le]⟩
    exact_mod_cast this
  have hdiv : (ρ / 2) ^ finrank ℝ V * unitBallVolume (finrank ℝ V) / ZLattice.covolume La ≤
      ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ) := (div_le_iff₀ hcpos).mpr hle'
  have hlog := Real.log_le_log (by have := unitBallVolume_pos (finrank ℝ V); positivity) hdiv
  rw [Real.log_div (by have := unitBallVolume_pos (finrank ℝ V); positivity) hcpos.ne',
    Real.log_mul (by positivity) (unitBallVolume_pos _).ne', Real.log_pow] at hlog
  linarith
end GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount
