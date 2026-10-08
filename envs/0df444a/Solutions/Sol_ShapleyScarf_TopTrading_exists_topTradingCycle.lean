-- Prove2me | solution 1 for ShapleyScarf.TopTrading.exists_topTradingCycle
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:23:28.100084+00:00
-- url     : https://prove2.me/submissions/afc792eb-ea38-4e0d-95f2-52521101a772

import Mathlib
import Definitions.Def_ShapleyScarf_TopTrading_Market
import Definitions.Def_ShapleyScarf_TopTrading_TopTradingCycle



namespace ShapleyScarf.TopTrading

theorem aff_core {N : Type*} [Fintype N] [DecidableEq N]
    (A : N → N → ℝ) (P : TTCPartition A) (π : Fin P.p → ℝ) (hπ : StrictAnti π)
    (hπpos : ∀ j, 0 < π j) (i : N) :
    π (P.stage (P.next i)) = π (P.stage i) ∧
      ∀ k, π (P.stage k) ≤ π (P.stage i) → P.stage i ≤ P.stage k := by
  refine ⟨?_, ?_⟩
  · have h := (P.isTopTradingCycle (P.stage i)).2.2.1 i (by simp)
    simp at h
    rw [h]
  · intro k hk
    by_contra hlt
    push_neg at hlt
    have := hπ hlt
    linarith

theorem best_core {N : Type*} [Fintype N] [DecidableEq N]
    (A : N → N → ℝ) (P : TTCPartition A) (S : Finset N) (i : N) (hi : i ∈ S)
    (hfirst : ∀ k ∈ S, P.stage i ≤ P.stage k) :
    ∀ k ∈ S, A i k ≤ A i (P.next i) := by
  intro k hk
  have h := (P.isTopTradingCycle (P.stage i)).2.2.2.2 i (by simp) k (by simpa using hfirst k hk)
  exact h

theorem ttc_congr {N : Type*} (A : N → N → ℝ) (R S : Finset N) (n1 n2 : N → N)
    (h : IsTopTradingCycle A R S n1) (he : ∀ i ∈ S, n1 i = n2 i) :
    IsTopTradingCycle A R S n2 := by
  obtain ⟨hne, hsub, hcl, hreach, hbest⟩ := h
  have hit : ∀ k, ∀ i ∈ S, n2^[k] i = n1^[k] i := by
    intro k
    induction k with
    | zero => intro i _; rfl
    | succ k ih =>
      intro i hi
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih i hi]
      have : n1^[k] i ∈ S := by
        clear ih
        induction k with
        | zero => simpa using hi
        | succ k ih2 => rw [Function.iterate_succ_apply']; exact hcl _ ih2
      exact (he _ this).symm
  refine ⟨hne, hsub, ?_, ?_, ?_⟩
  · intro i hi; rw [← he i hi]; exact hcl i hi
  · intro i hi i' hi'
    obtain ⟨k, hk⟩ := hreach i hi i' hi'
    exact ⟨k, by rw [hit k i hi]; exact hk⟩
  · intro i hi j hj; rw [← he i hi]; exact hbest i hi j hj

theorem exists_ttc_core {N : Type*} [Fintype N] [DecidableEq N] (A : N → N → ℝ)
    (R : Finset N) (hR : R.Nonempty) :
    ∃ (S : Finset N) (next : N → N), IsTopTradingCycle A R S next := by
  classical
  obtain ⟨i0, hi0⟩ := hR
  have hex : ∀ i : N, ∃ j ∈ R, ∀ j' ∈ R, A i j' ≤ A i j := fun i =>
    Finset.exists_max_image R (A i) ⟨i0, hi0⟩
  choose f hfR hfmax using hex
  have hit : ∀ k, f^[k] i0 ∈ R := by
    intro k
    induction k with
    | zero => simpa using hi0
    | succ k ih => rw [Function.iterate_succ_apply']; exact hfR _
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (⟨f^[k] i0, hit k⟩ : R))
  have heq' : f^[a] i0 = f^[b] i0 := congrArg Subtype.val heq
  wlog hlt : a < b generalizing a b
  · exact this b a hab.symm heq.symm heq'.symm (lt_of_le_of_ne (not_lt.mp hlt) hab.symm)
  set c := f^[a] i0 with hc
  set n := b - a with hn
  have hnpos : 0 < n := by omega
  have hcn : f^[n] c = c := by
    rw [hc, ← Function.iterate_add_apply]
    have : n + a = b := by omega
    rw [this]; exact heq'.symm
  have hcR : c ∈ R := hit a
  have hmem : ∀ k, f^[k] c ∈ R := by
    intro k
    induction k with
    | zero => simpa using hcR
    | succ k ih => rw [Function.iterate_succ_apply']; exact hfR _
  refine ⟨(Finset.range n).image (fun k => f^[k] c), f, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨c, Finset.mem_image.2 ⟨0, by simpa using hnpos, rfl⟩⟩
  · intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hx
    exact hmem k
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    refine Finset.mem_image.2 ⟨if k + 1 = n then 0 else k + 1, ?_, ?_⟩
    · have := Finset.mem_range.1 hk
      apply Finset.mem_range.2
      split_ifs <;> omega
    · split_ifs with h
      · rw [← Function.iterate_succ_apply' f k c, Nat.succ_eq_add_one, h, hcn]; rfl
      · simp [Function.iterate_succ_apply']
  · intro x hx y hy
    obtain ⟨a', ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b', hb, rfl⟩ := Finset.mem_image.1 hy
    have ha := Finset.mem_range.1 ha
    refine ⟨b' + (n - a'), ?_⟩
    rw [← Function.iterate_add_apply]
    have : b' + (n - a') + a' = b' + n := by omega
    rw [this, Function.iterate_add_apply, hcn]
  · intro x hx j hj
    exact hfmax x j hj

-- generalized ℕ-staged version
theorem exists_stages {N : Type*} [Fintype N] [DecidableEq N] (A : N → N → ℝ) :
    ∀ (m : ℕ) (R : Finset N), R.card = m →
      ∃ (p : ℕ) (stage : N → ℕ) (next : N → N), (∀ i ∈ R, stage i < p) ∧
        ∀ j < p, IsTopTradingCycle A (R.filter fun i => j ≤ stage i)
          (R.filter fun i => stage i = j) next := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro R hRm
    rcases R.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, fun _ => 0, id, by simp, by simp⟩
    · obtain ⟨S, n0, hS⟩ := exists_ttc_core A R hne
      have hlt : (R \ S).card < m := by
        rw [← hRm]
        apply Finset.card_lt_card
        exact ⟨Finset.sdiff_subset, fun h => by
          obtain ⟨x, hx⟩ := hS.1
          exact (Finset.mem_sdiff.1 (h (hS.2.1 hx))).2 hx⟩
      obtain ⟨p', st', n', hst', hc'⟩ := ih _ hlt (R \ S) rfl
      classical
      refine ⟨p' + 1, fun i => if i ∈ S then 0 else st' i + 1,
        fun i => if i ∈ S then n0 i else n' i, ?_, ?_⟩
      · intro i hi
        by_cases his : i ∈ S
        · simp [his]
        · simp [his]; exact hst' i (Finset.mem_sdiff.2 ⟨hi, his⟩)
      · intro j hj
        rcases j with _ | j
        · have h1 : R.filter (fun i => 0 ≤ (if i ∈ S then 0 else st' i + 1)) = R := by
            ext i; simp
          have h2 : R.filter (fun i => (if i ∈ S then 0 else st' i + 1) = 0) = S := by
            ext i
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨_, h⟩
              by_contra hs; simp [hs] at h
            · intro hs; exact ⟨hS.2.1 hs, by simp [hs]⟩
          rw [h1, h2]
          exact ttc_congr A R S n0 _ hS (fun i hi => by simp [hi])
        · have h1 : R.filter (fun i => j + 1 ≤ (if i ∈ S then 0 else st' i + 1))
              = (R \ S).filter (fun i => j ≤ st' i) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_sdiff]
            constructor
            · rintro ⟨hr, h⟩
              by_cases his : i ∈ S
              · simp [his] at h
              · simp [his] at h; exact ⟨⟨hr, his⟩, h⟩
            · rintro ⟨⟨hr, his⟩, h⟩; exact ⟨hr, by simp [his]; exact h⟩
          have h2 : R.filter (fun i => (if i ∈ S then 0 else st' i + 1) = j + 1)
              = (R \ S).filter (fun i => st' i = j) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_sdiff]
            constructor
            · rintro ⟨hr, h⟩
              by_cases his : i ∈ S
              · simp [his] at h
              · simp [his] at h; exact ⟨⟨hr, his⟩, h⟩
            · rintro ⟨⟨hr, his⟩, h⟩; exact ⟨hr, by simp [his]; exact h⟩
          rw [h1, h2]
          refine ttc_congr A _ _ n' _ (hc' j (by omega)) ?_
          intro i hi
          have : i ∈ R \ S := by
            have := (Finset.mem_filter.1 hi).1; exact this
          have his := (Finset.mem_sdiff.1 this).2
          simp [his]

theorem exists_part {N : Type*} [Fintype N] [DecidableEq N] (A : N → N → ℝ) :
    Nonempty (TTCPartition A) := by
  obtain ⟨p, st, nx, hst, hc⟩ := exists_stages A _ (Finset.univ : Finset N) rfl
  refine ⟨⟨p, fun i => ⟨st i, hst i (Finset.mem_univ i)⟩, nx, ?_⟩⟩
  intro j
  have := hc j j.2
  have e1 : (Finset.univ.filter fun i : N => j ≤ (⟨st i, hst i (Finset.mem_univ i)⟩ : Fin p))
      = Finset.univ.filter fun i : N => (j : ℕ) ≤ st i := by
    ext i; simp [Fin.le_def]
  have e2 : (Finset.univ.filter fun i : N => (⟨st i, hst i (Finset.mem_univ i)⟩ : Fin p) = j)
      = Finset.univ.filter fun i : N => st i = (j : ℕ) := by
    ext i; simp [Fin.ext_iff]
  rw [e1, e2]
  exact this

theorem bij_core {N : Type*} [Fintype N] [DecidableEq N]
    (A : N → N → ℝ) (P : TTCPartition A) : Function.Bijective P.next := by
  have hs : Function.Surjective P.next := by
    intro y
    have h := P.isTopTradingCycle (P.stage y)
    have hy : y ∈ Finset.univ.filter fun i => P.stage i = P.stage y := by simp
    have hny := h.2.2.1 y hy
    obtain ⟨k, hk⟩ := h.2.2.2.1 _ hny y hy
    cases k with
    | zero => exact ⟨y, by simpa using hk⟩
    | succ k =>
      refine ⟨P.next^[k] (P.next y), ?_⟩
      rw [← Function.iterate_succ_apply' P.next k]; exact hk
  exact ⟨Finite.injective_iff_surjective.2 hs, hs⟩

theorem ttc_core {N : Type*} [Fintype N] [DecidableEq N]
    (A : N → N → ℝ) (P : TTCPartition A) :
    IsCoreAllocation A P.next ∧
      ∀ π : Fin P.p → ℝ, StrictAnti π → (∀ j, 0 < π j) →
        IsCompetitive A P.next (fun k => π (P.stage k)) := by
  refine ⟨⟨bij_core A P, ?_⟩, ?_⟩
  · rintro ⟨S, τ, hne, hτ, _, hlt⟩
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image S P.stage hne
    have := best_core A P S i hi hmin (τ i) (hτ i hi)
    exact absurd (hlt i hi) (not_lt.2 this)
  · intro π hπ hpos
    refine ⟨bij_core A P, fun i => ⟨?_, ?_⟩⟩
    · exact ((aff_core A P π hπ hpos i).1).le
    · intro k hk
      have h1 := (aff_core A P π hπ hpos i).2 k hk
      exact best_core A P {i, k} i (by simp) (fun k' hk' => by
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · exact le_rfl
        · rw [Finset.mem_singleton.1 hk']; exact h1) k (by simp)

end ShapleyScarf.TopTrading

open ShapleyScarf.TopTrading


theorem solution {N : Type*} [Fintype N] [DecidableEq N] (A : N → N → ℝ)
    (R : Finset N) (hR : R.Nonempty) :
    ∃ (S : Finset N) (next : N → N), IsTopTradingCycle A R S next := by
  exact exists_ttc_core A R hR
