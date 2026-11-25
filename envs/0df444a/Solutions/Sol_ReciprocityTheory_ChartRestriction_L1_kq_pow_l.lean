-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kq_pow_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:04:00.837992+00:00
-- url     : https://prove2.me/submissions/e67a6338-2ced-46ff-8c0d-7307b57215c2

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
    (hn : ‖δ‖ = 1) : ‖δ ^ l + δ‖ ≤ ‖(l : ℂ_[l])‖ := by
  have hodd : l = 2 * (l / 2) + 1 := by
    have h2 := (Fact.out : l.Prime).mod_two_eq_one_iff_ne_two.mpr hl
    have h3 := Nat.div_add_mod l 2
    omega
  rw [kq_pow_odd δ _ hδ l (l / 2) hodd]
  have e : δ * (-(d : ℂ_[l])) ^ (l / 2) + δ = δ * ((((-(d : ℤ)) ^ (l / 2) + 1 : ℤ)) : ℂ_[l]) := by
    push_cast
    ring
  rw [e, norm_mul, hn, one_mul]
  apply kq_zmod
  push_cast
  rw [kq_euler l d hld hin]
  ring
end ReciprocityTheory.ChartRestriction.L1
