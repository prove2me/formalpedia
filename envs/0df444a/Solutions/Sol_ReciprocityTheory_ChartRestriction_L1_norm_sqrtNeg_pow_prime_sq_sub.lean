-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_sqrtNeg_pow_prime_sq_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:14:33.529421+00:00
-- url     : https://prove2.me/submissions/3b228bc5-49b3-44e8-9c2c-632d86db4372

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormSqrtNegPowPrimeSqSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_zmod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_euler
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_pow_odd

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
variable {l}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (d : ℕ) (hl : l ≠ 2) (hld : ¬ l ∣ d)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) (δ : ℂ_[l]) (hδ : δ ^ 2 = -(d : ℂ_[l]))
    (hn : ‖δ‖ = 1) : ‖δ ^ (l ^ 2) - δ‖ ≤ ‖(l : ℂ_[l])‖ := by
  have hodd : l = 2 * (l / 2) + 1 := by
    have := (Fact.out : l.Prime).eq_two_or_odd
    omega
  have e0 : δ ^ l = δ * (((-(d : ℤ)) ^ (l / 2) : ℤ) : ℂ_[l]) := by
    rw [kq_pow_odd δ _ hδ l (l / 2) hodd]
    push_cast
    ring
  have e : δ ^ (l ^ 2) - δ = δ * ((((-(d : ℤ)) ^ (l / 2)) ^ (l + 1) - 1 : ℤ) : ℂ_[l]) := by
    rw [sq, pow_mul, e0, mul_pow, e0]
    push_cast
    ring
  rw [e, norm_mul, hn, one_mul]
  apply kq_zmod
  push_cast
  rw [kq_euler l d hld hin]
  have : l + 1 = 2 * (l / 2 + 1) := by omega
  rw [this, pow_mul]
  simp
end ReciprocityTheory.ChartRestriction.L1
