-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TBDisc.normFam_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:28.483074+00:00
-- url     : https://prove2.me/submissions/a6889f43-b42f-469e-b481-e56150e9a271

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_RatIntUnifDiscrete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_UniformDiscreteness_FgOfUnifDiscrete
import Theorems.Thm_PI_UnitaryGroupMassFormula_TBDisc_normFam_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TBDisc
open NumberField ReciprocityTheory.ChartRestriction.G.TB
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
namespace PI.UnitaryGroupMassFormula.TBDisc
theorem _root_.solution (Nf : NormFam K V) (σ : K →+* ℂ) {ι : Type*} (s : Finset ι)
    (g : ι → V) : Nf.N σ (∑ i ∈ s, g i) ≤ ∑ i ∈ s, Nf.N σ (g i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [normFam_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Nf.add σ _ _).trans (by linarith)
end PI.UnitaryGroupMassFormula.TBDisc
