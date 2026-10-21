-- Prove2me | solution 1 for PromoMulti.PairwiseExact.pairwise_sum_higher_zero
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:43:40.676982+00:00
-- url     : https://prove2.me/submissions/8f2598ea-bb37-45f2-9043-5a1265811637

import Mathlib
set_option autoImplicit false

theorem solution {n m : ℕ} (A : Fin m → Finset (Fin n))
    (hA : ∀ r, (A r).card ≤ 2) (g : Fin m → (Fin n → Bool) → ℝ)
    (hg : ∀ r (x y : Fin n → Bool), (∀ i ∈ A r, x i = y i) → g r x = g r y)
    (S : Finset (Fin n)) (hS : 3 ≤ S.card) :
    ∑ U ∈ S.powerset, (-1 : ℝ) ^ (S.card - U.card) * ∑ r, g r (fun i => decide (i ∈ U)) = 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun r _ => ?_
  have hne : (S \ A r).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.le_card_sdiff (A r) S
    have := hA r
    omega
  obtain ⟨s, hs⟩ := hne
  rw [Finset.mem_sdiff] at hs
  obtain ⟨hsS, hsA⟩ := hs
  have hS' : S = insert s (S.erase s) := (Finset.insert_erase hsS).symm
  have hcard : (S.erase s).card + 1 = S.card := Finset.card_erase_add_one hsS
  set T := S.erase s with hT
  have hsT : s ∉ T := Finset.notMem_erase s S
  rw [hS', Finset.sum_powerset_insert hsT]
  rw [← hS'] at *
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun t ht => ?_
  rw [Finset.mem_powerset] at ht
  have htT : t.card ≤ T.card := Finset.card_le_card ht
  have hst : s ∉ t := fun h => hsT (ht h)
  have hg' : g r (fun i => decide (i ∈ insert s t)) = g r (fun i => decide (i ∈ t)) := by
    apply hg
    intro i hi
    have : i ≠ s := fun h => hsA (h ▸ hi)
    simp [this]
  rw [hg', Finset.card_insert_of_notMem hst, ← hcard]
  have : T.card + 1 - t.card = (T.card - t.card) + 1 := by omega
  have h2 : T.card + 1 - (t.card + 1) = T.card - t.card := by omega
  rw [this, h2, pow_succ]
  ring
