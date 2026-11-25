-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.rmu_sigma_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:41:37.106829+00:00
-- url     : https://prove2.me/submissions/19fe63cb-5911-4a88-a9b0-ef63cc2612cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_prime_lt_one_padicField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_prime_pos_padicField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_frobeniusLift_norm_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kmu_shape
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rmu_le_kmu
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rmu_norm_le


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
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ‖((s x : Rmu l) : ℂ_[l])‖ = ‖(x : ℂ_[l])‖ := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx0' : (x : ℂ_[l]) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨m, a, ha, b, hb, hna, hnb, h⟩ := kmu_shape l (rmu_le_kmu l x.2) hx0'
  have hb0 : b ≠ 0 := by intro h0; rw [h0, norm_zero] at hnb; exact zero_ne_one hnb
  have hn : ‖(x : ℂ_[l])‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [h, norm_mul, norm_zpow, norm_div, hna, hnb]; simp
  have hm : 0 ≤ m := by
    by_contra hneg
    rw [not_le] at hneg
    have : 1 < ‖(l : ℂ_[l])‖ ^ m :=
      one_lt_zpow_of_neg₀ (norm_prime_pos_padicField l) (norm_prime_lt_one_padicField l) hneg
    rw [← hn] at this
    exact absurd (rmu_norm_le l x.2) (not_le.mpr this)
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  have he : x * (⟨b, hb⟩ : Rmu l) = (l : Rmu l) ^ k * (⟨a, ha⟩ : Rmu l) := by
    apply Subtype.ext
    push_cast
    rw [h, zpow_natCast]
    field_simp
  have hs' := congrArg (fun z : Rmu l => ‖(z : ℂ_[l])‖) (congrArg s he)
  simp only [map_mul, map_pow, map_natCast] at hs'
  push_cast at hs'
  rw [norm_mul, norm_mul, norm_pow, frobeniusLift_norm_one l s hs ⟨b, hb⟩ hnb,
    frobeniusLift_norm_one l s hs ⟨a, ha⟩ hna, mul_one, mul_one] at hs'
  rw [hs', hn, zpow_natCast]
end ReciprocityTheory.ChartRestriction.L1
