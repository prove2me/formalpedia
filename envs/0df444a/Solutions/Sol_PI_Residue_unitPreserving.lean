-- Prove2me | solution 1 for PI.Residue.unitPreserving
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:40.245287+00:00
-- url     : https://prove2.me/submissions/8ccc053a-b852-490b-b43a-4a3342263425

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BoxEqConvexBodyLT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitMulDetNeZero
import Theorems.Thm_PI_Residue_unitMul_det_ne_zero
import Theorems.Thm_PI_Residue_preimage_box
import Theorems.Thm_PI_Residue_prod_inv_unit
import Theorems.Thm_PI_Residue_vfac_ne_zero
import Theorems.Thm_PI_Residue_vfac_ne_top
import Theorems.Thm_PI_Residue_boxVolume


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
open scoped ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable (K : Type) [Field K] [NumberField K]
namespace PI.Residue
theorem _root_.solution : UnitPreserving := by
  intro K _ _ u
  have hdet := unitMul_det_ne_zero K u
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (mixedSpace K)) hdet
  have hpre := Measure.addHaar_preimage_linearMap
    (volume : Measure (mixedSpace K)) hdet (box K fun _ => 1)
  have hw : ∀ w : InfinitePlace K, 0 < (w (u : K))⁻¹ := fun w =>
    inv_pos.2 (w.pos_iff.2 (by simp))
  rw [preimage_box, boxVolume K _ hw, boxVolume K _ (fun _ => one_pos), prod_inv_unit] at hpre
  simp only [one_pow, Finset.prod_const_one, ENNReal.ofReal_one, mul_one] at hpre
  have hc : ENNReal.ofReal |(LinearMap.det (unitMul K u))⁻¹| = 1 :=
    (ENNReal.mul_left_inj (vfac_ne_zero K) (vfac_ne_top K)).1 (by rw [one_mul]; exact hpre.symm)
  rw [hc, one_smul] at hmap
  exact ⟨(unitMul K u).continuous_of_finiteDimensional.measurable, hmap⟩
end PI.Residue
