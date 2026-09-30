-- Prove2me | solution 1 for SupplyChainTheory.vcg_core_characterization
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T22:26:13.161021+00:00
-- url     : https://prove2.me/submissions/fee0438f-8400-470a-b05a-2bcd0dd3dc5f

import Mathlib
import Definitions.Def_SupplyChainTheory_auctions

open SupplyChainTheory

theorem solution {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ)
    (hV : IsCoalitionalValue V) :
    (BidderSubmodular V ↔ ∀ S : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∈ S → ∀ π,
        InCore V S π ↔ (∑ k ∈ S, π k = V S ∧ ∀ k ∈ S, k ≠ 0 → 0 ≤ π k ∧ π k ≤ vcgPayoff V S k))
      ∧ (BidderSubmodular V ↔ ∀ S : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∈ S →
          InCore V S (vcgPayoff V S)) := by
  classical
  obtain ⟨hV0, hVmono⟩ := hV
  have hvcg : ∀ S k, k ≠ 0 → vcgPayoff V S k = V S - V (S.erase k) :=
    fun S k hk => by rw [vcgPayoff, if_neg hk]
  have hvcg0 : ∀ S k, k ≠ 0 → 0 ≤ vcgPayoff V S k :=
    fun S k hk => by rw [hvcg S k hk]; exact sub_nonneg.mpr (hVmono (Finset.erase_subset _ _))
  -- The VCG payoffs of a coalition add up to its value.
  have hsum : ∀ S, (0 : Fin (n + 1)) ∈ S → ∑ k ∈ S, vcgPayoff V S k = V S := by
    intro S h0
    rw [← Finset.add_sum_erase _ _ h0, vcgPayoff, if_pos rfl,
      Finset.sum_congr rfl (fun l hl => hvcg S l (Finset.ne_of_mem_erase hl))]
    ring
  -- (ii) with its easy half: core vectors always lie in `Π_S`.
  have hcore_Pi : ∀ S, ∀ π, InCore V S π →
      ∀ k ∈ S, k ≠ 0 → 0 ≤ π k ∧ π k ≤ vcgPayoff V S k := by
    intro S π ⟨hπsum, hπ⟩ k hk hk0
    refine ⟨?_, ?_⟩
    · have := hπ {k} (Finset.singleton_subset_iff.mpr hk)
      rwa [hV0 _ (by simpa using Ne.symm hk0), Finset.sum_singleton] at this
    · have h := hπ (S.erase k) (Finset.erase_subset _ _)
      have hsplit := Finset.add_sum_erase S π hk
      rw [hvcg S k hk0]; linarith
  -- **(i) ⇒ (ii).** Telescoping marginal contributions from `T` up to `S`.
  have h12 : BidderSubmodular V → ∀ S : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∈ S → ∀ π,
      InCore V S π ↔ (∑ k ∈ S, π k = V S ∧ ∀ k ∈ S, k ≠ 0 → 0 ≤ π k ∧ π k ≤ vcgPayoff V S k) := by
    intro hsm S h0 π
    refine ⟨fun hπ => ⟨hπ.1, hcore_Pi S π hπ⟩, fun ⟨hπsum, hπb⟩ => ⟨hπsum, fun T hTS => ?_⟩⟩
    by_cases hT0 : (0 : Fin (n + 1)) ∈ T
    · have htel : ∀ U : Finset (Fin (n + 1)), U ⊆ S \ T →
          ∑ k ∈ U, (V S - V (S.erase k)) ≤ V (T ∪ U) - V T := by
        intro U
        induction U using Finset.induction_on with
        | empty => intro _; simp
        | @insert a U haU ih =>
          intro hU
          have ha : a ∈ S \ T := hU (Finset.mem_insert_self a U)
          rw [Finset.mem_sdiff] at ha
          have hU' : U ⊆ S \ T := fun x hx => hU (Finset.mem_insert_of_mem hx)
          have ha0 : a ≠ 0 := fun h => ha.2 (h ▸ hT0)
          have hsub : T ∪ U ⊆ S.erase a := by
            intro x hx
            rw [Finset.mem_erase]
            rcases Finset.mem_union.mp hx with hx | hx
            · exact ⟨fun h => ha.2 (h ▸ hx), hTS hx⟩
            · exact ⟨fun h => haU (h ▸ hx), (Finset.mem_sdiff.mp (hU' hx)).1⟩
          have h := hsm a ha0 (T ∪ U) (S.erase a) (Finset.mem_union_left _ hT0) hsub
          rw [Finset.insert_erase ha.1] at h
          rw [Finset.sum_insert haU, Finset.union_insert]
          linarith [ih hU']
      have h1 := htel (S \ T) le_rfl
      rw [Finset.union_sdiff_of_subset hTS] at h1
      have h2 : ∑ k ∈ S \ T, π k ≤ ∑ k ∈ S \ T, (V S - V (S.erase k)) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hk0 : k ≠ 0 := fun h => (Finset.mem_sdiff.mp hk).2 (h ▸ hT0)
        rw [← hvcg S k hk0]; exact (hπb k (Finset.mem_sdiff.mp hk).1 hk0).2
      have h3 := Finset.sum_sdiff hTS (f := π)
      linarith
    · rw [hV0 T hT0]
      refine Finset.sum_nonneg (fun k hk => (hπb k (hTS hk) (fun h => hT0 (h ▸ hk))).1)
  -- **(ii) ⇒ (iii).** The VCG vector lies in `Π_S`.
  have h23 : (∀ S : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∈ S → ∀ π,
      InCore V S π ↔ (∑ k ∈ S, π k = V S ∧ ∀ k ∈ S, k ≠ 0 → 0 ≤ π k ∧ π k ≤ vcgPayoff V S k)) →
      ∀ S : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∈ S → InCore V S (vcgPayoff V S) :=
    fun h2 S h0 => (h2 S h0 _).mpr ⟨hsum S h0, fun k _ hk => ⟨hvcg0 S k hk, le_rfl⟩⟩
  -- **(iii) ⇒ (i).** The coalition `A` blocks the VCG vector of `A ∪ {j, k}` unless the
  -- single-step inequality holds; single steps then chain to full submodularity.
  have h31 : (∀ S : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∈ S → InCore V S (vcgPayoff V S)) →
      BidderSubmodular V := by
    intro h3
    have hlocal : ∀ A : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∈ A → ∀ j k, j ∉ A → k ∉ A →
        j ≠ k → V (insert j (insert k A)) - V (insert k A) ≤ V (insert j A) - V A := by
      intro A h0 j k hj hk hjk
      have hj0 : j ≠ 0 := fun h => hj (h ▸ h0)
      have hk0 : k ≠ 0 := fun h => hk (h ▸ h0)
      set S := insert j (insert k A) with hS
      have hjS : j ∉ insert k A := by rw [Finset.mem_insert]; push Not; exact ⟨hjk, hj⟩
      have hcore := h3 S (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h0))
      have hblock := hcore.2 A (fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
      have htot := hcore.1
      rw [hS, Finset.sum_insert hjS, Finset.sum_insert hk, ← hS] at htot
      have hej : S.erase j = insert k A := by rw [hS, Finset.erase_insert hjS]
      have hek : S.erase k = insert j A := by
        rw [hS, Finset.erase_insert_of_ne hjk, Finset.erase_insert hk]
      rw [hvcg S j hj0, hvcg S k hk0, hej, hek] at htot
      linarith
    intro k hk S S' h0 hSS'
    by_cases hkS' : k ∈ S'
    · rw [Finset.insert_eq_of_mem hkS', sub_self]
      exact sub_nonneg.mpr (hVmono (Finset.subset_insert _ _))
    have hchain : ∀ U : Finset (Fin (n + 1)), U ⊆ S' \ S →
        V (insert k (S ∪ U)) - V (S ∪ U) ≤ V (insert k S) - V S := by
      intro U
      induction U using Finset.induction_on with
      | empty => intro _; simp
      | @insert a U haU ih =>
        intro hU
        have ha := Finset.mem_sdiff.mp (hU (Finset.mem_insert_self a U))
        have hU' : U ⊆ S' \ S := fun x hx => hU (Finset.mem_insert_of_mem hx)
        have haSU : a ∉ S ∪ U := by
          rw [Finset.mem_union]; push Not; exact ⟨ha.2, haU⟩
        have hkSU : k ∉ S ∪ U := by
          rw [Finset.mem_union]; push Not
          exact ⟨fun h => hkS' (hSS' h), fun h => hkS' (Finset.mem_sdiff.mp (hU' h)).1⟩
        have hak : a ≠ k := fun h => hkS' (h ▸ ha.1)
        have hl := hlocal (S ∪ U) (Finset.mem_union_left _ h0) a k haSU hkSU hak
        rw [Finset.union_insert, Finset.insert_comm k a]
        linarith [ih hU']
    have := hchain (S' \ S) le_rfl
    rwa [Finset.union_sdiff_of_subset hSS'] at this
  exact ⟨⟨h12, fun h2 => h31 (h23 h2)⟩, ⟨fun h1 => h23 (h12 h1), h31⟩⟩
