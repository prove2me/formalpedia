-- Prove2me | solution 1 for PI.RhsWLim.W.sum_wb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:59:59.176326+00:00
-- url     : https://prove2.me/submissions/dc1d5202-ad4e-47e5-84ff-bb07c1e54e74

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Theorems.Thm_PI_RhsWLim_W_wI_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → f i = 0) :
    ∑ i, f i = ∑ j : Fin (k + 1), f (wI k r j) := by
  have h1 : ∑ j : Fin (k + 1), f (PI.RhsWLim.wI k r j) = ∑ i ∈ Finset.univ.image (PI.RhsWLim.wI k r), f i :=
    (Finset.sum_image (fun a _ b _ h => wI_injective h)).symm
  rw [h1]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro i _ hi
  apply hf
  by_contra hc
  apply hi
  rw [Finset.mem_image]
  exact ⟨⟨i.val - r, by omega⟩, Finset.mem_univ _, Fin.ext (by simp only [PI.RhsWLim.wI]; omega)⟩
end PI.RhsWLim.W
