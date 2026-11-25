-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ChooseW.scaled_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:41:21.579073+00:00
-- url     : https://prove2.me/submissions/30646ece-0fde-472d-a1a3-a2805c0d7ed7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_Choose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.ChooseW
variable {K : Type*} [Field K] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.LCG.ChooseW
theorem _root_.solution {ι : Type*} {V : Type*} [AddCommGroup V] [Module K V] (d : ι → V) (m : ι → K)
    (hm : ∀ c, m c ≠ 0) :
    Submodule.span K (Set.range d) ≤ Submodule.span K (Set.range fun c => m c • d c) := by
  rw [Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have : d c = (m c)⁻¹ • (m c • d c) := by rw [smul_smul, inv_mul_cancel₀ (hm c), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
end PI.UnitaryGroupMassFormula.LCG.ChooseW
