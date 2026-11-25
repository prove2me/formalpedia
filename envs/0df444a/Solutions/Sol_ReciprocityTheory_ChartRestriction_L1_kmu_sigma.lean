-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kmu_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:18:36.042933+00:00
-- url     : https://prove2.me/submissions/21e315cd-7db3-4044-9e7f-3653b25b6c3f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_frobeniusLift_near_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_frobeniusLift_norm_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_unitBall_eq_frac_normOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rmu_sigma_norm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_exists_extend_endomorphism_fractions
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_frobeniusLift_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_unramifiedField_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kmu_frac
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rmu_le_kmu
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rmu_sigma


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
theorem _root_.solution : ∃ s : Kmu l →+* Kmu l, (∀ x : Kmu l, ‖s x‖ = ‖x‖) ∧
    ∀ x : Kmu l, ‖x‖ ≤ 1 → ‖s x - x ^ l‖ ≤ ‖(l : Kmu l)‖ := by
  obtain ⟨s, hs⟩ := rmu_sigma l
  obtain ⟨σ, key⟩ := exists_extend_endomorphism_fractions (Rmu l) (Kmu l) (fun _ hx => rmu_le_kmu l hx)
    (fun _ hx => kmu_frac l hx) s (frobeniusLift_injective l s hs)
  refine ⟨σ, ?_, ?_⟩
  · intro x
    obtain ⟨a, ha, b, hb, hb0, h⟩ := kmu_frac l x.2
    have h1 : (x : ℂ_[l]) * b = a := by rw [h]; field_simp
    have h2 := key x ⟨a, ha⟩ ⟨b, hb⟩ h1
    have h3 := congrArg norm h2
    have h4 := congrArg norm h1
    rw [norm_mul, rmu_sigma_norm l s hs, rmu_sigma_norm l s hs] at h3
    rw [norm_mul] at h4
    have hb' : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb0
    rw [norm_unramifiedField_coe, norm_unramifiedField_coe]
    exact mul_right_cancel₀ hb' (h3.trans h4.symm)
  · intro x hx
    rw [norm_unramifiedField_coe] at hx
    obtain ⟨a, ha, b, hb, hnb, h1⟩ := unitBall_eq_frac_normOne l x.2 hx
    have h2 := key x ⟨a, ha⟩ ⟨b, hb⟩ h1
    have hsb := frobeniusLift_norm_one l s hs ⟨b, hb⟩ hnb
    have hna := frobeniusLift_near_pow l s hs ⟨a, ha⟩
    have hnb' := frobeniusLift_near_pow l s hs ⟨b, hb⟩
    rw [norm_unramifiedField_coe, norm_unramifiedField_coe, Subfield.coe_sub, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
    generalize ((s ⟨a, ha⟩ : Rmu l) : ℂ_[l]) = sa at h2 hna
    generalize ((s ⟨b, hb⟩ : Rmu l) : ℂ_[l]) = sb at h2 hnb' hsb
    generalize ((σ x : Kmu l) : ℂ_[l]) = y at h2 ⊢
    simp only at hna hnb'
    have e : (y - (x : ℂ_[l]) ^ l) * sb = (sa - a ^ l) + -((x : ℂ_[l]) ^ l * (sb - b ^ l)) := by
      rw [← h1, ← h2]; ring
    have hxl : ‖(x : ℂ_[l]) ^ l‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    have e2 : ‖(y - (x : ℂ_[l]) ^ l)‖ = ‖(sa - a ^ l) + -((x : ℂ_[l]) ^ l * (sb - b ^ l))‖ := by
      rw [← e, norm_mul, hsb, mul_one]
    rw [e2]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hna ?_)
    rw [norm_neg, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hxl).trans hnb'
end ReciprocityTheory.ChartRestriction.L1
