-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.squarefree_count_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:06:42.950574+00:00
-- url     : https://prove2.me/submissions/a119d70c-ef2a-4b19-97c7-d609675ed1d4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_SquarefreeCountEstimate
import Theorems.Thm_PI_SqfPrimeFactor_W_card_bad
import Theorems.Thm_PI_SqfPrimeFactor_W_mem_bad
import Theorems.Thm_PI_SqfPrimeFactor_W_bad_disj
import Theorems.Thm_PI_SqfPrimeFactor_W_T_disj
import Theorems.Thm_PI_SqfPrimeFactor_W_card_monicDeg
import Theorems.Thm_PI_SqfPrimeFactor_W_mem_monicDeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
open PI.SqfLab
namespace PI.SqfPrimeFactor.W
theorem _root_.solution : CountA := by
  intro g r _ T hT
  classical
  set B := (bigPrimes r).biUnion (fun p => bad g r p) with hB
  have hsub : T ∪ B ⊆ monicDeg g r := by
    intro f hf
    rcases Finset.mem_union.1 hf with hf | hf
    · obtain ⟨⟨hm, hd, -⟩, -, -⟩ := hT f hf
      exact mem_monicDeg.2 ⟨hm, hd⟩
    · obtain ⟨p, hp, hfb⟩ := Finset.mem_biUnion.1 hf
      obtain ⟨q, h, rfl, hqm, hqd, hqi, hhm, hhd⟩ := mem_bad hfb
      obtain ⟨hpp, h2p, hp3⟩ := (Finset.mem_filter.1 hp).2
      refine mem_monicDeg.2 ⟨hqm.mul hhm, ?_⟩
      rw [hqm.natDegree_mul hhm]
      omega
  have hdisj : Disjoint T B := by
    rw [hB, Finset.disjoint_biUnion_right]
    intro p hp
    exact T_disj r p hp T hT
  have hcardB : B.card = ∑ p ∈ bigPrimes r, (irrDeg g p).card * g ^ (r - p) := by
    rw [hB, Finset.card_biUnion]
    · refine Finset.sum_congr rfl (fun p hp => ?_)
      obtain ⟨_, h2p, _⟩ := (Finset.mem_filter.1 hp).2
      exact card_bad r p h2p
    · intro p hp p' hp' hne
      obtain ⟨_, h2p, _⟩ := (Finset.mem_filter.1 hp).2
      obtain ⟨_, h2p', _⟩ := (Finset.mem_filter.1 hp').2
      exact bad_disj h2p h2p' hne
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hcardB, card_monicDeg] at h1
  have h2 : ((T.card + ∑ p ∈ bigPrimes r, (irrDeg g p).card * g ^ (r - p) : ℕ) : ℝ)
      ≤ ((g ^ r : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  linarith
end PI.SqfPrimeFactor.W
