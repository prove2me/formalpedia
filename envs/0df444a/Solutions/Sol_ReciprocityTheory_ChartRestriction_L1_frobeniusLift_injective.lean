-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.frobeniusLift_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:05:57.623927+00:00
-- url     : https://prove2.me/submissions/9ab8d4b2-790d-4773-9cb6-71f3557ed843

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rmu_sigma_norm

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
theorem _root_.solution (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) : Function.Injective s := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have := rmu_sigma_norm l s hs x
  rw [hx, Subring.coe_zero, norm_zero] at this
  exact Subtype.ext (norm_eq_zero.mp this.symm)
end ReciprocityTheory.ChartRestriction.L1
