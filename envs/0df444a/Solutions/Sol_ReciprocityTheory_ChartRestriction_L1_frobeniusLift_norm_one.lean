-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.frobeniusLift_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:54:19.626333+00:00
-- url     : https://prove2.me/submissions/71ea4fba-b75b-4dbd-9d71-8a7cd75e8316

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_prime_lt_one_padicField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_frobeniusLift_near_pow

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
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l)
    (hx : ‖(x : ℂ_[l])‖ = 1) : ‖((s x : Rmu l) : ℂ_[l])‖ = 1 := by
  have h1 : ‖(x : ℂ_[l]) ^ l‖ = 1 := by rw [norm_pow, hx, one_pow]
  have h2 : ‖((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l‖ < ‖(x : ℂ_[l]) ^ l‖ := by
    rw [h1]; exact lt_of_le_of_lt (frobeniusLift_near_pow l s hs x) (norm_prime_lt_one_padicField l)
  have h3 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt h2)
  rw [sub_add_cancel, max_eq_right h2.le, h1] at h3
  exact h3
end ReciprocityTheory.ChartRestriction.L1
