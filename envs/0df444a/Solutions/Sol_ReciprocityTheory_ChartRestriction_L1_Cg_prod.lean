-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Cg.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:11.165428+00:00
-- url     : https://prove2.me/submissions/32032d76-bf90-4ebe-b8f9-9de322c9f83b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Cg_refl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Cg_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LowUnit_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LowUnit_one


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
namespace Cg
theorem _root_.solution {p : ℕ} {α : Type*} (s : Finset α) (f g : α → PowerSeries ℂ)
    (h : ∀ t ∈ s, Cg p (f t) (g t)) : Cg p (∏ t ∈ s, f t) (∏ t ∈ s, g t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Cg.refl (CoeffIn.one _)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun t ht => h t (Finset.mem_insert_of_mem ht))
end Cg
end ReciprocityTheory.ChartRestriction.L1
