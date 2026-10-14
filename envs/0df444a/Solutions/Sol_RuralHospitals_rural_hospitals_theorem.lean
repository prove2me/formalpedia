-- Prove2me | solution 1 for RuralHospitals.rural_hospitals_theorem
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-11T21:29:33.092002+00:00
-- url     : https://prove2.me/submissions/a417b019-bd1c-4d51-bb77-14eb5bed8b80

import Mathlib
import Definitions.Def_RuralHospitals_Market

set_option autoImplicit false

open RuralHospitals Finset

namespace RH_a

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]

omit [Fintype H] in
theorem mem_assigned {μ : Assignment D H} {h : H} {d : D} :
    d ∈ assigned μ h ↔ μ d = some h := by
  simp [assigned]

/-- F1: a doctor strictly preferring `μ` to `ν` is matched under `μ`. -/
theorem F1 (M : Market D H) (μ ν : Assignment D H) (hν : M.IsStable ν) (d : D)
    (hd : M.docRank d (μ d) < M.docRank d (ν d)) : ∃ h, μ d = some h := by
  cases hμd : μ d with
  | none =>
    exfalso
    rw [hμd] at hd
    have := hν.2.1.1 d
    omega
  | some h => exact ⟨h, rfl⟩

/-- F2: consequences of `(d, h)` not blocking `ν`. -/
theorem F2 (M : Market D H) (μ ν : Assignment D H) (hμ : M.IsStable μ) (hν : M.IsStable ν)
    (d : D) (h : H) (hd : M.docRank d (μ d) < M.docRank d (ν d)) (hμd : μ d = some h) :
    (assigned ν h).card = M.capacity h ∧
      ∀ d' ∈ assigned ν h, M.hospRank h (some d') < M.hospRank h (some d) := by
  have hnb := hν.2.2 d h
  have h1 : M.docRank d (some h) < M.docRank d (ν d) := by rw [← hμd]; exact hd
  have h2 : M.hospRank h (some d) < M.hospRank h none := hμ.2.1.2 d h hμd
  have h3 : ¬ ((assigned ν h).card < M.capacity h ∨
      ∃ d' ∈ assigned ν h, M.hospRank h (some d) < M.hospRank h (some d')) :=
    fun h3 => hnb ⟨h1, h2, h3⟩
  push Not at h3
  refine ⟨le_antisymm (hν.1 h) h3.1, fun d' hd' => ?_⟩
  have hle := h3.2 d' hd'
  have hne : d' ≠ d := by
    rintro rfl
    rw [mem_assigned] at hd'
    rw [hd', hμd] at hd
    exact lt_irrefl _ hd
  have hne' : M.hospRank h (some d') ≠ M.hospRank h (some d) := by
    intro heq
    exact hne (Option.some_injective _ (M.hospRank_injective h heq))
  omega

/-- F3: key exchange argument. -/
theorem F3 (M : Market D H) (μ ν : Assignment D H) (hμ : M.IsStable μ) (hν : M.IsStable ν)
    (h : H) (d₀ : D) (hd₀ : M.docRank d₀ (μ d₀) < M.docRank d₀ (ν d₀)) (hμd₀ : μ d₀ = some h)
    (d : D) (hνd : ν d = some h) (hne : μ d ≠ ν d) :
    M.docRank d (μ d) < M.docRank d (ν d) := by
  rcases lt_trichotomy (M.docRank d (μ d)) (M.docRank d (ν d)) with hlt | heq | hgt
  · exact hlt
  · exact absurd (M.docRank_injective d heq) hne
  · exfalso
    have a := (F2 M ν μ hν hμ d h hgt hνd).2 d₀ (mem_assigned.2 hμd₀)
    have b := (F2 M μ ν hμ hν d₀ h hd₀ hμd₀).2 d (mem_assigned.2 hνd)
    omega

/-- Core lemma (F4, C1, C2). -/
theorem core (M : Market D H) (μ ν : Assignment D H) (hμ : M.IsStable μ) (hν : M.IsStable ν) :
    (∀ d, M.docRank d (μ d) < M.docRank d (ν d) →
      ∃ h', ν d = some h' ∧ ∃ d', μ d' = some h' ∧ M.docRank d' (μ d') < M.docRank d' (ν d')) ∧
    (∀ h, (∃ d, μ d = some h ∧ M.docRank d (μ d) < M.docRank d (ν d)) →
      (assigned μ h).card = (assigned ν h).card ∧ (assigned ν h).card = M.capacity h) := by
  classical
  set S : Finset H := univ.filter
    (fun h => ∃ d, μ d = some h ∧ M.docRank d (μ d) < M.docRank d (ν d)) with hS
  have memS : ∀ h, h ∈ S ↔ ∃ d, μ d = some h ∧ M.docRank d (μ d) < M.docRank d (ν d) := by
    intro h; simp [hS]
  have disj : ∀ (σ : Assignment D H), (S : Set H).PairwiseDisjoint (assigned σ) := by
    intro σ x _ y _ hxy
    show Disjoint (assigned σ x) (assigned σ y)
    rw [Finset.disjoint_left]
    intro d hx hy
    rw [mem_assigned] at hx hy
    exact hxy (Option.some_injective _ (hx.symm.trans hy))
  have cardμ := Finset.card_biUnion (disj μ)
  have cardν := Finset.card_biUnion (disj ν)
  have hsub : S.biUnion (assigned ν) ⊆ S.biUnion (assigned μ) := by
    intro d hd
    rw [Finset.mem_biUnion] at hd ⊢
    obtain ⟨h, hhS, hdh⟩ := hd
    rw [mem_assigned] at hdh
    by_cases heq : μ d = ν d
    · exact ⟨h, hhS, mem_assigned.2 (heq.trans hdh)⟩
    · obtain ⟨d₀, hμd₀, hd₀⟩ := (memS h).1 hhS
      have hp := F3 M μ ν hμ hν h d₀ hd₀ hμd₀ d hdh heq
      obtain ⟨h'', hh''⟩ := F1 M μ ν hν d hp
      exact ⟨h'', (memS h'').2 ⟨d, hh'', hp⟩, mem_assigned.2 hh''⟩
  have hpt : ∀ h ∈ S, (assigned μ h).card ≤ (assigned ν h).card := by
    intro h hh
    obtain ⟨d₀, hμd₀, hd₀⟩ := (memS h).1 hh
    rw [(F2 M μ ν hμ hν d₀ h hd₀ hμd₀).1]
    exact hμ.1 h
  have hsum : ∑ h ∈ S, (assigned μ h).card ≤ ∑ h ∈ S, (assigned ν h).card :=
    Finset.sum_le_sum hpt
  have hcardle := Finset.card_le_card hsub
  have hEq : S.biUnion (assigned ν) = S.biUnion (assigned μ) :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hsumeq : ∑ h ∈ S, (assigned μ h).card = ∑ h ∈ S, (assigned ν h).card := by omega
  refine ⟨fun d hd => ?_, fun h hh => ?_⟩
  · obtain ⟨h, hμd⟩ := F1 M μ ν hν d hd
    have hmem : d ∈ S.biUnion (assigned μ) :=
      Finset.mem_biUnion.2 ⟨h, (memS h).2 ⟨d, hμd, hd⟩, mem_assigned.2 hμd⟩
    rw [← hEq, Finset.mem_biUnion] at hmem
    obtain ⟨h', hh'S, hdh'⟩ := hmem
    exact ⟨h', mem_assigned.1 hdh', (memS h').1 hh'S⟩
  · have hhS : h ∈ S := (memS h).2 hh
    obtain ⟨d₀, hμd₀, hd₀⟩ := hh
    refine ⟨?_, (F2 M μ ν hμ hν d₀ h hd₀ hμd₀).1⟩
    exact (Finset.sum_eq_sum_iff_of_le hpt).1 hsumeq h hhS

end RH_a

/-- **Rural hospitals theorem.** -/
theorem solution {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]
    (M : Market D H) (μ ν : Assignment D H) (hμ : M.IsStable μ) (hν : M.IsStable ν) :
    (∀ d, (μ d).isSome = (ν d).isSome) ∧
      (∀ h, (assigned μ h).card = (assigned ν h).card) ∧
      ∀ h, (assigned μ h).card < M.capacity h → assigned ν h = assigned μ h := by
  obtain ⟨P1, P2⟩ := RH_a.core M μ ν hμ hν
  obtain ⟨N1, N2⟩ := RH_a.core M ν μ hν hμ
  have hassign : ∀ h, ¬ (∃ d, μ d = some h ∧ M.docRank d (μ d) < M.docRank d (ν d)) →
      ¬ (∃ d, ν d = some h ∧ M.docRank d (ν d) < M.docRank d (μ d)) →
      assigned ν h = assigned μ h := by
    intro h hp hn
    ext d
    rw [RH_a.mem_assigned, RH_a.mem_assigned]
    rcases lt_trichotomy (M.docRank d (μ d)) (M.docRank d (ν d)) with hlt | heq | hgt
    · constructor
      · intro hνd
        obtain ⟨h', hνd', hh'⟩ := P1 d hlt
        rw [hνd] at hνd'
        obtain rfl := Option.some_injective _ hνd'
        exact absurd hh' hp
      · intro hμd
        exact absurd ⟨d, hμd, hlt⟩ hp
    · rw [M.docRank_injective d heq]
    · constructor
      · intro hνd
        exact absurd ⟨d, hνd, hgt⟩ hn
      · intro hμd
        obtain ⟨h', hμd', hh'⟩ := N1 d hgt
        rw [hμd] at hμd'
        obtain rfl := Option.some_injective _ hμd'
        exact absurd hh' hn
  refine ⟨fun d => ?_, fun h => ?_, fun h hlt => ?_⟩
  · rcases lt_trichotomy (M.docRank d (μ d)) (M.docRank d (ν d)) with hlt | heq | hgt
    · obtain ⟨h, hμd⟩ := RH_a.F1 M μ ν hν d hlt
      obtain ⟨h', hνd, _⟩ := P1 d hlt
      simp [hμd, hνd]
    · rw [M.docRank_injective d heq]
    · obtain ⟨h, hνd⟩ := RH_a.F1 M ν μ hμ d hgt
      obtain ⟨h', hμd, _⟩ := N1 d hgt
      simp [hμd, hνd]
  · by_cases hp : ∃ d, μ d = some h ∧ M.docRank d (μ d) < M.docRank d (ν d)
    · exact (P2 h hp).1
    · by_cases hn : ∃ d, ν d = some h ∧ M.docRank d (ν d) < M.docRank d (μ d)
      · exact (N2 h hn).1.symm
      · rw [hassign h hp hn]
  · by_cases hp : ∃ d, μ d = some h ∧ M.docRank d (μ d) < M.docRank d (ν d)
    · have := P2 h hp
      omega
    · by_cases hn : ∃ d, ν d = some h ∧ M.docRank d (ν d) < M.docRank d (μ d)
      · have := N2 h hn
        omega
      · exact hassign h hp hn
