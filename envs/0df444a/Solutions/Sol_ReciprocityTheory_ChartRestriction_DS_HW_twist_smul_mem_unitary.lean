-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.twist_smul_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:34.992407+00:00
-- url     : https://prove2.me/submissions/2912c2d8-3ff8-4401-9984-e552107fd4fa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelTwist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] {s : ℂ}
    (hs : star s * s = 1) {A : V →L[ℂ] V} (hA : A ∈ unitary (V →L[ℂ] V)) :
    s • A ∈ unitary (V →L[ℂ] V) := by
  exact Unitary.smul_mem_of_mem (Unitary.mem_iff.2 ⟨hs, by rw [mul_comm]; exact hs⟩) hA
end ReciprocityTheory.ChartRestriction.DS.HW
