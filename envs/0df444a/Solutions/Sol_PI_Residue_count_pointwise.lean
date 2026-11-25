-- Prove2me | solution 1 for PI.Residue.count_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:36.092401+00:00
-- url     : https://prove2.me/submissions/97652a9c-a81e-4452-ab41-e8f2ebfda780

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_LatticeCountGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_NormAtPlacePosOfNormPos
import Theorems.Thm_PI_Residue_measurableSet_box
import Theorems.Thm_PI_Residue_normAtPlace_pos_of_norm_pos
import Theorems.Thm_PI_Residue_prod_radius
import Theorems.Thm_PI_Residue_mem_hit_of_mem_sub
import Theorems.Thm_PI_Residue_latticeCount


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
theorem _root_.solution (hB : BoxVolume) (J : (Ideal (𝓞 K))⁰) {ρ : ℝ} (hρ : 0 < ρ)
    {y : mixedSpace K} (hy : y ∈ shell K) :
    vfac K * ENNReal.ofReal ((ρ / 2) ^ Module.finrank ℚ K) ≤
      (∑' x : lat K J, (hit K ρ (x : mixedSpace K)).indicator (fun _ => (1 : ℝ≥0∞)) y) *
        ENNReal.ofReal (ZLattice.covolume (lat K J)) := by
  have hy0 : 0 < mixedEmbedding.norm y := lt_trans (by norm_num) hy.2.1
  set r : InfinitePlace K → ℝ := fun w => ρ / (2 * normAtPlace w y) with hr
  have hrpos : ∀ w, 0 < r w := fun w =>
    div_pos hρ (mul_pos two_pos (normAtPlace_pos_of_norm_pos hy0 w))
  have hvol := hB K r hrpos
  rw [hr, prod_radius] at hvol
  have hcount := latticeCount K (lat K J) (box K r) (measurableSet_box K r)
  have h1 : vfac K * ENNReal.ofReal ((ρ / 2) ^ Module.finrank ℚ K) ≤ volume (box K r) := by
    rw [hr, hvol]
    gcongr
    rw [le_div_iff₀ hy0]
    have hp : 0 ≤ (ρ / 2) ^ Module.finrank ℚ K := by positivity
    nlinarith [hy.2.2]
  refine h1.trans (hcount.trans ?_)
  gcongr with x
  by_cases hx : (x : mixedSpace K) ∈ box K r - box K r
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (mem_hit_of_mem_sub hy0 hx)]
  · rw [Set.indicator_of_notMem hx]
    exact zero_le
end PI.Residue
