-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kmuIncl_denseRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:38:17.675252+00:00
-- url     : https://prove2.me/submissions/ddd667a4-33d3-4ede-a3ec-d1093b4f0a68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KmuInclDenseRange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kur_approx


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution : DenseRange (kmuIncl l) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro e he
  obtain ⟨y, hy, hxy⟩ := kur_approx l x.2 e he
  exact ⟨kmuIncl l ⟨y, hy⟩, ⟨_, rfl⟩, by rw [dist_eq_norm]; exact hxy⟩
end ReciprocityTheory.ChartRestriction.L1
