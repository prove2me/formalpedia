-- Prove2me | solution 1 for PI.Residue.mem_hit_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:34.082283+00:00
-- url     : https://prove2.me/submissions/966005e7-82ce-4476-a5e0-3e98c53a5072

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BUnfold

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
theorem _root_.solution (ρ : ℝ) (u : (𝓞 K)ˣ) (x y : mixedSpace K) :
    y ∈ hit K ρ (u • x) ↔ u • y ∈ hit K ρ x := by
  simp only [hit, Set.mem_ofPred_eq, unitSMul_smul, map_mul]
  refine forall_congr' fun w => ?_
  rw [mul_left_comm, mul_assoc]
end PI.Residue
