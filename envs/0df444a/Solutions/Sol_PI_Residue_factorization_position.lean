-- Prove2me | solution 1 for PI.Residue.factorization_position
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:18:57.168911+00:00
-- url     : https://prove2.me/submissions/29098c6e-f9c8-4255-bd04-f1847ada0fd4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
import Theorems.Thm_PI_Residue_factorization_multiset_prod

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
    {s : Multiset α} (hs : ∀ a ∈ s, a ∈ S) {a : α} (ha : a ∈ S) :
    (intersection_update_fsHerm_neg_one N idx s (idx a)).factorization (N a).minFac
      = s.count a * (N a).factorization (N a).minFac := by
  have hp : (N a).minFac.Prime := Nat.minFac_prime (h1 a ha).ne'
  unfold intersection_update_fsHerm_neg_one
  rw [factorization_multiset_prod, Multiset.map_map,
    Multiset.sum_map_eq_nsmul_single a,
    Multiset.count_filter_of_pos (p := fun b => idx b = idx a) rfl]
  · simp
  · intro b hba hb
    rw [Multiset.mem_filter] at hb
    simp only [Function.comp_apply]
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    apply hba
    refine h2 b (hs b hb.1) a ha hb.2 ?_
    intro hcop
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hdvd (Nat.minFac_dvd _) hcop
  · intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    rw [Multiset.mem_filter] at hb
    exact (Nat.zero_lt_of_lt (h1 b (hs b hb.1))).ne'
end PI.Residue
