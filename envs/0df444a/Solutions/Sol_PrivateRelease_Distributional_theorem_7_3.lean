-- Prove2me | solution 1 for PrivateRelease.Distributional.theorem_7_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T04:23:55.499618+00:00
-- url     : https://prove2.me/submissions/44642248-4e98-4af7-9138-a5d730e6b5d7

import Mathlib
import Definitions.Def_PrivateRelease_Distributional_Privacy

set_option autoImplicit false

open MeasureTheory Filter Topology PrivateRelease.Distributional in
theorem solution {X R : Type} [DecidableEq X] [MeasurableSpace R] (A : ℕ → Finset X → Measure R)
    (β : ℕ → ℝ) (ε : ℝ) (hβ : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * β n) atTop (𝓝 0))
    (hA : ∀ n, IsDistPrivate (A n) n ε (β n)) :
    ∀ᶠ n in atTop, IsDPSet (A n) n ε := by
  have h1 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 * β n < 1 / 4 :=
    hβ.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [h1, eventually_ge_atTop 1] with n hn hn1
  intro D D' hN E hE
  by_contra hcon
  obtain ⟨hD, hD', hdiff⟩ := hN
  have hS : (D ∪ D').card = n + 1 := by
    rw [← Finset.card_sdiff_add_card, hdiff, hD']; ring
  have hbad : ¬ GoodPair (A n) ε D D' := fun h => hcon (h E hE)
  have hcount : 0 < badPairCount (A n) n ε (D ∪ D') := by
    unfold badPairCount
    apply Finset.card_pos.mpr
    refine ⟨(D, D'), ?_⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard]
    exact ⟨⟨⟨Finset.subset_union_left, hD⟩, ⟨Finset.subset_union_right, hD'⟩⟩, hbad⟩
  have key := hA n (D ∪ D') (by omega)
  rw [hS, Nat.choose_succ_self_right] at key
  have hc : (1 : ℝ) ≤ (badPairCount (A n) n ε (D ∪ D') : ℝ) := by exact_mod_cast hcount
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  push_cast at key
  rcases le_or_gt 0 (β n) with hb | hb
  · have : ((n : ℝ) + 1) ^ 2 * β n ≤ 4 * ((n : ℝ) ^ 2 * β n) := by
      have : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
      nlinarith
    nlinarith
  · have : β n * ((n : ℝ) + 1) ^ 2 < 0 := mul_neg_of_neg_of_pos hb (by positivity)
    linarith
