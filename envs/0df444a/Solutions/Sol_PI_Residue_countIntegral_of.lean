-- Prove2me | solution 1 for PI.Residue.countIntegral_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:19.355841+00:00
-- url     : https://prove2.me/submissions/6f77b968-a63d-4802-98a3-3532d01e8378

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_LatticeCountGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_NormAtPlacePosOfNormPos
import Theorems.Thm_PI_Residue_measurableSet_hit
import Theorems.Thm_PI_Residue_measurableSet_shell
import Theorems.Thm_PI_Residue_count_pointwise

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable (K : Type) [Field K] [NumberField K]
variable {K}
namespace PI.Residue
theorem _root_.solution (hB : BoxVolume) : CountIntegral := by
  intro K _ _ J ρ hρ
  have hm : ∀ x : lat K J, Measurable
      (fun y => (hit K ρ (x : mixedSpace K)).indicator (fun _ => (1 : ℝ≥0∞)) y) :=
    fun x => measurable_const.indicator (measurableSet_hit K ρ x)
  calc vfac K * ENNReal.ofReal ((ρ / 2) ^ Module.finrank ℚ K) * volume (shell K)
      = ∫⁻ _ in shell K, vfac K * ENNReal.ofReal ((ρ / 2) ^ Module.finrank ℚ K) := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ y in shell K,
          (∑' x : lat K J, (hit K ρ (x : mixedSpace K)).indicator (fun _ => (1 : ℝ≥0∞)) y) *
            ENNReal.ofReal (ZLattice.covolume (lat K J)) :=
        setLIntegral_mono' (measurableSet_shell K) fun y hy => count_pointwise hB J hρ hy
    _ = (∫⁻ y in shell K,
          (∑' x : lat K J, (hit K ρ (x : mixedSpace K)).indicator (fun _ => (1 : ℝ≥0∞)) y)) *
            ENNReal.ofReal (ZLattice.covolume (lat K J)) :=
        lintegral_mul_const _ (Measurable.tsum hm)
    _ = (∑' x : lat K J, volume (shell K ∩ hit K ρ (x : mixedSpace K))) *
          ENNReal.ofReal (ZLattice.covolume (lat K J)) := by
        rw [lintegral_tsum fun x => (hm x).aemeasurable]
        congr 1
        refine tsum_congr fun x => ?_
        rw [lintegral_indicator_const (measurableSet_hit K ρ x), one_mul,
          Measure.restrict_apply (measurableSet_hit K ρ x), Set.inter_comm]
  exact le_rfl
end PI.Residue
