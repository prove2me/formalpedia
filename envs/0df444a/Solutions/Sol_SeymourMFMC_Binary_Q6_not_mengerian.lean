-- Prove2me | solution 1 for SeymourMFMC.Binary.Q6_not_mengerian
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-30T14:10:32.148892+00:00
-- url     : https://prove2.me/submissions/ead6dd6f-f6a0-476c-9b08-ea3d72ebaf75

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Definitions.Def_SeymourMFMC_Binary_Q6
import Definitions.Def_SeymourMFMC_Binary_IsMengerian
import Definitions.Def_SeymourMFMC_Binary_ground
import Definitions.Def_SeymourMFMC_Binary_blocker
import Definitions.Def_SeymourMFMC_Binary_Meets

open SeymourMFMC.Binary

-- Seymour 1977, Section 1, p. 193: Q₆ is not Mengerian.
-- With the all-ones weight, every integral packing has value ≤ 1 (any two
-- members share an element, and singletons overload), while every blocker
-- member has weight ≥ 2 (no empty or singleton transversal exists).
theorem solution : ¬ IsMengerian Q6 := by
  have hne : Q6 ≠ {∅} := by decide
  have hQ : Q6 = ({{0, 2, 4}, {0, 3, 5}, {1, 2, 5}, {1, 3, 4}} :
      Finset (Finset (Fin 6))) := rfl
  intro h
  unfold IsMengerian at h
  obtain hL | hw := h
  · exact hne hL
  · obtain ⟨q, hcap, B, hBmem, heq, -⟩ := hw (fun _ => 1)
    have e0 : (0 : Fin 6) ∈ ground Q6 := by decide
    have e1 : (1 : Fin 6) ∈ ground Q6 := by decide
    have e2 : (2 : Fin 6) ∈ ground Q6 := by decide
    have e3 : (3 : Fin 6) ∈ ground Q6 := by decide
    have e4 : (4 : Fin 6) ∈ ground Q6 := by decide
    have e5 : (5 : Fin 6) ∈ ground Q6 := by decide
    have f0 : Q6.filter (fun A => (0 : Fin 6) ∈ A) =
        ({{0, 2, 4}, {0, 3, 5}} : Finset (Finset (Fin 6))) := by decide
    have f1 : Q6.filter (fun A => (1 : Fin 6) ∈ A) =
        ({{1, 2, 5}, {1, 3, 4}} : Finset (Finset (Fin 6))) := by decide
    have f2 : Q6.filter (fun A => (2 : Fin 6) ∈ A) =
        ({{0, 2, 4}, {1, 2, 5}} : Finset (Finset (Fin 6))) := by decide
    have f3 : Q6.filter (fun A => (3 : Fin 6) ∈ A) =
        ({{0, 3, 5}, {1, 3, 4}} : Finset (Finset (Fin 6))) := by decide
    have f4 : Q6.filter (fun A => (4 : Fin 6) ∈ A) =
        ({{0, 2, 4}, {1, 3, 4}} : Finset (Finset (Fin 6))) := by decide
    have f5 : Q6.filter (fun A => (5 : Fin 6) ∈ A) =
        ({{0, 3, 5}, {1, 2, 5}} : Finset (Finset (Fin 6))) := by decide
    have c0 : q {0, 2, 4} + q {0, 3, 5} ≤ 1 := by
      have h := hcap (0 : Fin 6) e0
      rwa [f0, Finset.sum_pair
        (show ({0, 2, 4} : Finset (Fin 6)) ≠ {0, 3, 5} by decide)] at h
    have c1 : q {1, 2, 5} + q {1, 3, 4} ≤ 1 := by
      have h := hcap (1 : Fin 6) e1
      rwa [f1, Finset.sum_pair
        (show ({1, 2, 5} : Finset (Fin 6)) ≠ {1, 3, 4} by decide)] at h
    have c2 : q {0, 2, 4} + q {1, 2, 5} ≤ 1 := by
      have h := hcap (2 : Fin 6) e2
      rwa [f2, Finset.sum_pair
        (show ({0, 2, 4} : Finset (Fin 6)) ≠ {1, 2, 5} by decide)] at h
    have c3 : q {0, 3, 5} + q {1, 3, 4} ≤ 1 := by
      have h := hcap (3 : Fin 6) e3
      rwa [f3, Finset.sum_pair
        (show ({0, 3, 5} : Finset (Fin 6)) ≠ {1, 3, 4} by decide)] at h
    have c4 : q {0, 2, 4} + q {1, 3, 4} ≤ 1 := by
      have h := hcap (4 : Fin 6) e4
      rwa [f4, Finset.sum_pair
        (show ({0, 2, 4} : Finset (Fin 6)) ≠ {1, 3, 4} by decide)] at h
    have c5 : q {0, 3, 5} + q {1, 2, 5} ≤ 1 := by
      have h := hcap (5 : Fin 6) e5
      rwa [f5, Finset.sum_pair
        (show ({0, 3, 5} : Finset (Fin 6)) ≠ {1, 2, 5} by decide)] at h
    have hB2 : 2 ≤ B.card := by
      -- NB: `B ∈ blocker Q6` must be opened via `simp only [Finset.mem_filter]`
      -- (instance metavariables assigned by matching, no TC synthesis). `rw` or
      -- `.mp` with `Finset.mem_filter` instead lets the elaborator re-synthesize
      -- the filter's `DecidablePred` by TC after unification; server-side (full
      -- Mathlib in scope) that yields the `Fintype.decidableForallFintype` form,
      -- which is not defeq to the `Finset.decidableDforallFinset` form stored in
      -- the platform definition, failing `_check` (three CEs diagnosed this).
      simp only [blocker, Finset.mem_filter] at hBmem
      obtain ⟨-, hMeets, -⟩ := hBmem
      have hM : ∀ A ∈ Q6, (A ∩ B).Nonempty := hMeets
      have m1 := hM {0, 2, 4} (by decide)
      have m2 := hM {0, 3, 5} (by decide)
      have m3 := hM {1, 2, 5} (by decide)
      by_contra hlt
      have hlt : B.card < 2 := not_le.mp hlt
      by_cases hB0 : B = ∅
      · subst hB0
        obtain ⟨y, hy⟩ := m1
        exact (Finset.notMem_empty y) ((Finset.mem_inter.mp hy).2)
      · have hne0 : B.card ≠ 0 := fun hz => hB0 (Finset.card_eq_zero.mp hz)
        have h10 : B.card = 1 := by
          have hpos : 0 < B.card := Nat.pos_of_ne_zero hne0
          omega
        obtain ⟨x0, hx0⟩ := Finset.card_eq_one.mp h10
        obtain ⟨y1, hy1⟩ := m1
        obtain ⟨y2, hy2⟩ := m2
        obtain ⟨y3, hy3⟩ := m3
        rw [Finset.mem_inter] at hy1 hy2 hy3
        rw [hx0] at hy1 hy2 hy3
        have g1 : y1 = x0 := Finset.mem_singleton.mp hy1.2
        have g2 : y2 = x0 := Finset.mem_singleton.mp hy2.2
        have g3 : y3 = x0 := Finset.mem_singleton.mp hy3.2
        rw [g1] at hy1
        rw [g2] at hy2
        rw [g3] at hy3
        have hcon : x0 ∈ ((({0, 2, 4} ∩ {0, 3, 5} ∩ {1, 2, 5}) : Finset (Fin 6))) :=
          Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hy1.1, hy2.1⟩, hy3.1⟩
        have hempty : ((({0, 2, 4} ∩ {0, 3, 5} ∩ {1, 2, 5}) : Finset (Fin 6))) = ∅ := by
          decide
        rw [hempty] at hcon
        exact Finset.notMem_empty x0 hcon
    have hwt : (∑ x ∈ B, (fun _ => 1) x) = B.card := by simp
    rw [hQ, Finset.sum_insert
      (show ({0, 2, 4} : Finset (Fin 6)) ∉
        ({{0, 3, 5}, {1, 2, 5}, {1, 3, 4}} : Finset (Finset (Fin 6))) by decide),
      Finset.sum_insert
      (show ({0, 3, 5} : Finset (Fin 6)) ∉
        ({{1, 2, 5}, {1, 3, 4}} : Finset (Finset (Fin 6))) by decide),
      Finset.sum_insert
      (show ({1, 2, 5} : Finset (Fin 6)) ∉
        ({{1, 3, 4}} : Finset (Finset (Fin 6))) by decide),
      Finset.sum_singleton, hwt] at heq
    omega
