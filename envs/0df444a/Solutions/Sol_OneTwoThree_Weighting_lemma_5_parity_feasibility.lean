-- Prove2me | solution 1 for OneTwoThree.Weighting.lemma_5_parity_feasibility
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-12T00:39:55.764108+00:00
-- url     : https://prove2.me/submissions/1a5d61c3-8f53-4a23-86fb-b53adb1d89d5

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

set_option autoImplicit false

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (α : V → ℕ) (d : V → ℕ)
    (hα : ∀ v ∈ B, (α v : ℤ) = 2 * (d v : ℤ) - 1 ∨ (α v : ℤ) = 2 * (d v : ℤ) ∨
      (α v : ℤ) = 2 * (d v : ℤ) + 1)
    (R' : Finset V) (hR' : R' ⊆ Bᶜ)
    (hpar : Even (Finset.card R' + Finset.sum B (fun v => α v))) :
    Even (Finset.card (R' ∪ B.filter (fun v => α v ≠ 2 * d v))) := by
  have hodd : ∀ v ∈ B, (α v ≠ 2 * d v) ↔ Odd (α v) := by
    intro v hv
    rcases hα v hv with h | h | h
    · have h2 : α v = 2 * (d v - 1) + 1 := by omega
      constructor
      · intro _
        exact ⟨d v - 1, h2⟩
      · intro _ hcon
        have hc : (α v : ℤ) = 2 * (d v : ℤ) := by exact_mod_cast hcon
        omega
    · have h2 : α v = 2 * d v := by omega
      constructor
      · intro hne
        exact absurd h2 hne
      · intro ho hcon
        rw [hcon] at ho
        exact Nat.not_odd_iff_even.mpr ⟨d v, by ring⟩ ho
    · have h2 : α v = 2 * d v + 1 := by omega
      constructor
      · intro _
        exact ⟨d v, h2⟩
      · intro _ hcon
        have hc : (α v : ℤ) = 2 * (d v : ℤ) := by exact_mod_cast hcon
        omega
  have hfeq : B.filter (fun v => α v ≠ 2 * d v) = B.filter (fun v => Odd (α v)) :=
    Finset.filter_congr fun v hv => hodd v hv
  have hdisj : Disjoint R' (B.filter (fun v => α v ≠ 2 * d v)) := by
    rw [Finset.disjoint_left]
    intro x hxR hxF
    rw [Finset.mem_filter] at hxF
    exact (Finset.mem_compl.mp (hR' hxR)) hxF.1
  have hparsum : Even (B.filter (fun v => Odd (α v))).card ↔
      Even (Finset.sum B (fun v => α v)) := by
    have h := Finset.even_sum_iff_even_card_odd (s := B) (fun v => α v)
    simpa using h.symm
  have key : Even (Finset.card R') ↔ Even (B.filter (fun v => Odd (α v))).card := by
    have h2 := Nat.even_add.mp hpar
    rwa [← hparsum] at h2
  rw [Finset.card_union_of_disjoint hdisj, hfeq, Nat.even_add]
  exact key

/-- Alias under the published node name: the platform verifier looks up the
    published theorem name in the submission environment (dual-naming recipe). -/
theorem OneTwoThree.Weighting.lemma_5_parity_feasibility {V : Type*} [Fintype V]
    [DecidableEq V]
    (B : Finset V) (α : V → ℕ) (d : V → ℕ)
    (hα : ∀ v ∈ B, (α v : ℤ) = 2 * (d v : ℤ) - 1 ∨ (α v : ℤ) = 2 * (d v : ℤ) ∨
      (α v : ℤ) = 2 * (d v : ℤ) + 1)
    (R' : Finset V) (hR' : R' ⊆ Bᶜ)
    (hpar : Even (Finset.card R' + Finset.sum B (fun v => α v))) :
    Even (Finset.card (R' ∪ B.filter (fun v => α v ≠ 2 * d v))) :=
  solution B α d hα R' hR' hpar
