-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.IsMF.conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:47:14.008489+00:00
-- url     : https://prove2.me/submissions/b8646cf6-a7ce-4b4d-a960-16cb10494e4a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_qm_surj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_hasSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_hasSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_summable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_conv_of_hasSum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
namespace IsMF
theorem _root_.solution {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) : Conv (qExpansion 1 f) := by
  apply conv_of_hasSum
  intro x hx
  by_cases h0 : x = 0
  · subst h0
    exact (hasSum_single 0 fun n hn => by simp [zero_pow hn]).summable
  · obtain ⟨τ, hτ⟩ := qm_surj one_pos (norm_pos_iff.mpr h0) hx
    rw [← hτ]
    exact (hf.hasSum τ).summable
end IsMF
end ReciprocityTheory.ChartRestriction.L1
