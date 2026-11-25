-- Prove2me | solution 1 for PI.Residue.position_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:23:49.014322+00:00
-- url     : https://prove2.me/submissions/d7fcccd4-a0ec-487e-a8bd-ca2e7c533496

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
import Theorems.Thm_PI_Residue_factorization_position

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open scoped ENNReal
variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]
namespace PI.Residue
theorem _root_.solution (N : α → ℕ) (idx : α → ι) (S : Set α) (h1 : ∀ a ∈ S, 1 < N a)
    (h2 : ∀ a ∈ S, ∀ b ∈ S, idx a = idx b → ¬ Nat.Coprime (N a) (N b) → a = b)
    {s t : Multiset α} (hs : ∀ a ∈ s, a ∈ S) (ht : ∀ a ∈ t, a ∈ S)
    (h : intersection_update_fsHerm_neg_one N idx s = intersection_update_fsHerm_neg_one N idx t) : s = t := by
  ext a
  by_cases ha : a ∈ S
  · have e1 := factorization_position N idx S h1 h2 hs ha
    have e2 := factorization_position N idx S h1 h2 ht ha
    rw [h, e2] at e1
    have hp : (N a).minFac.Prime := Nat.minFac_prime (h1 a ha).ne'
    have hpos : 0 < (N a).factorization (N a).minFac :=
      hp.factorization_pos_of_dvd (Nat.zero_lt_of_lt (h1 a ha)).ne' (Nat.minFac_dvd _)
    exact (Nat.eq_of_mul_eq_mul_right hpos e1).symm
  · rw [Multiset.count_eq_zero_of_notMem (fun h' => ha (hs a h')),
      Multiset.count_eq_zero_of_notMem (fun h' => ha (ht a h'))]
end PI.Residue
