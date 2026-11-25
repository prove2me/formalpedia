-- Prove2me | solution 1 for PI.Residue.preimage_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:13:01.150295+00:00
-- url     : https://prove2.me/submissions/e119e021-f316-4b35-a535-db050d9cb3f0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BoxEqConvexBodyLT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitMulDetNeZero
import Theorems.Thm_PI_Residue_unitMul_apply

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
theorem _root_.solution (u : (𝓞 K)ˣ) :
    (unitMul K u) ⁻¹' (box K fun _ => 1) = box K (fun w => (w (u : K))⁻¹) := by
  ext y
  simp only [Set.mem_preimage, box, Set.mem_ofPred_eq, unitMul_apply, unitSMul_smul, map_mul,
    normAtPlace_apply]
  refine forall_congr' fun w => ?_
  have hw : 0 < w (u : K) := by
    refine w.pos_iff.2 ?_
    simp
  rw [← one_div, lt_div_iff₀' hw]
end PI.Residue
