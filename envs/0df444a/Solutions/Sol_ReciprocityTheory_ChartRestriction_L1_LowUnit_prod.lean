-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.LowUnit.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:47:12.453794+00:00
-- url     : https://prove2.me/submissions/4a365ef3-ddcb-4e3c-8dc8-2c51a5efc551

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LowUnit_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LowUnit_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_mul


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
namespace LowUnit
theorem _root_.solution {R : Subring ℂ} {α : Type*} (s : Finset α) (f : α → PowerSeries ℂ)
    (hf : ∀ t ∈ s, ∃ n u, LowUnit R (f t) n u) : ∃ n u, LowUnit R (∏ t ∈ s, f t) n u := Finset.prod_induction f (fun g => ∃ n u, ReciprocityTheory.ChartRestriction.L1.LowUnit R g n u)
    (fun a b ⟨n, u, ha⟩ ⟨n', u', hb⟩ => ⟨n + n', u * u', ReciprocityTheory.ChartRestriction.L1.LowUnit.mul ha hb⟩)
    ⟨0, 1, ReciprocityTheory.ChartRestriction.L1.LowUnit.one R⟩ hf
end LowUnit
end ReciprocityTheory.ChartRestriction.L1
