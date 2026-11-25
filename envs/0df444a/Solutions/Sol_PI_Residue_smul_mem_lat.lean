-- Prove2me | solution 1 for PI.Residue.smul_mem_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:13:28.036573+00:00
-- url     : https://prove2.me/submissions/0389bcb1-a50d-4487-99f4-f73cf5edb3dd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BUnfold
import Theorems.Thm_PI_Residue_mem_lat

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
variable {K : Type} [Field K] [NumberField K]
namespace PI.Residue
theorem _root_.solution {J : (Ideal (𝓞 K))⁰} {x : mixedSpace K} (u : (𝓞 K)ˣ) (hx : x ∈ lat K J) :
    u • x ∈ lat K J := by
  obtain ⟨a, ha, rfl⟩ := mem_lat.1 hx
  refine mem_lat.2 ⟨u * a, Ideal.mul_mem_left _ _ ha, ?_⟩
  rw [unitSMul_smul]
  simp [map_mul]
end PI.Residue
