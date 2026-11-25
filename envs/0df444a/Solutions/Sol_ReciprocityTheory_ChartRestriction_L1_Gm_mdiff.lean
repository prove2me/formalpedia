-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Gm_mdiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:56:45.539526+00:00
-- url     : https://prove2.me/submissions/03ae48c9-2b00-4654-a774-338a155eae24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmSlash
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmForm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_fac_mdiff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Tm_pos


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
theorem _root_.solution {m : ℕ} (hm : 0 < m) : MDiff (Gm m) := by
  unfold Gm
  have key : ∀ s : Finset (ℕ × ℕ × ℕ), s ⊆ Tm m → MDiff (fun τ => ∏ t ∈ s, fac t τ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa using (mdifferentiable_const : MDiff (fun _ : ℍ => (1 : ℂ)))
    | insert t s ht ih =>
      intro hs
      simp only [Finset.prod_insert ht]
      exact (fac_mdiff (Tm_pos hm (hs (Finset.mem_insert_self t s)))).mul
        (ih (fun x hx => hs (Finset.mem_insert_of_mem hx)))
  exact key _ subset_rfl
end ReciprocityTheory.ChartRestriction.L1
