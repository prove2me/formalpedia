-- Prove2me | solution 2 for SandsSauerWoodrow.two_coloured_tournament_sink
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T02:05:33.615517+00:00
-- url     : https://prove2.me/submissions/896d6d2f-b93b-4d51-ae14-718b414f2eeb

import Mathlib
import Definitions.Def_opg1808_colored_tournaments

open OPG1808

universe u

namespace SSWAux


variable {V : Type u} (D : OPG1808.Digraph V) (color : OPG1808.ArcColoring V)

theorem fin3_two : ∀ a b d : Fin 3, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) → (d = 0 ∨ d = 1) →
    b ≠ a → d = a ∨ d = b := by decide

theorem finset_sink' [DecidableEq V] (P : Set V)
    (htour : ∀ u v, u ∈ P → v ∈ P → u ≠ v → D u v ∨ D v u)
    (htwo : ∀ u v, D u v → (color u v = 0 ∨ color u v = 1)) :
    ∀ (S : Finset V), (↑S : Set V) ⊆ P → S.Nonempty →
      ∃ v ∈ S, ∀ x ∈ S, x ≠ v → MonochromaticallyReaches D color x v := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  intro hSP hne
  by_contra hcon
  push Not at hcon
  -- each x ∈ S has a sink of S.erase x
  have key : ∀ x ∈ S, ∃ y, y ∈ S ∧ y ≠ x ∧
      (∀ z ∈ S, z ≠ x → z ≠ y → MonochromaticallyReaches D color z y) ∧
      ¬ MonochromaticallyReaches D color x y ∧ D y x := by
    intro x hx
    have hne' : (S.erase x).Nonempty := by
      obtain ⟨w, hw, hw', _⟩ := hcon x hx
      exact ⟨w, Finset.mem_erase.2 ⟨hw', hw⟩⟩
    obtain ⟨y, hy, hyr⟩ := ih (S.erase x) (Finset.erase_ssubset hx)
      (fun z hz => hSP (Finset.mem_of_mem_erase hz)) hne'
    obtain ⟨hyx, hyS⟩ := Finset.mem_erase.1 hy
    have hr : ∀ z ∈ S, z ≠ x → z ≠ y → MonochromaticallyReaches D color z y :=
      fun z hz hzx hzy => hyr z (Finset.mem_erase.2 ⟨hzx, hz⟩) hzy
    have hnx : ¬ MonochromaticallyReaches D color x y := by
      intro h
      obtain ⟨w, hw, hw', hwr⟩ := hcon y hyS
      apply hwr
      by_cases hwx : w = x
      · subst hwx; exact h
      · exact hr w hw hwx hw'
    refine ⟨y, hyS, hyx, hr, hnx, ?_⟩
    rcases htour x y (hSP hx) (hSP hyS) (Ne.symm hyx) with h | h
    · exfalso; apply hnx
      exact ⟨color x y, Relation.ReflTransGen.single ⟨h, rfl⟩⟩
    · exact h
  classical
  let s : V → V := fun x => if hx : x ∈ S then Classical.choose (key x hx) else x
  have hs : ∀ x ∈ S, s x ∈ S ∧ s x ≠ x ∧
      (∀ z ∈ S, z ≠ x → z ≠ s x → MonochromaticallyReaches D color z (s x)) ∧
      ¬ MonochromaticallyReaches D color x (s x) ∧ D (s x) x := by
    intro x hx
    have := Classical.choose_spec (key x hx)
    simp only [s, dif_pos hx]
    exact this
  obtain ⟨x0, hx0⟩ := hne
  let xs : ℕ → V := fun n => s^[n] x0
  have hsucc : ∀ n, xs (n + 1) = s (xs n) := fun n =>
    Function.iterate_succ_apply' s n x0
  have hmem : ∀ n, xs n ∈ S := by
    intro n
    induction n with
    | zero => exact hx0
    | succ n ihn => rw [hsucc]; exact (hs _ ihn).1
  have hS : ∀ n, xs (n + 1) ≠ xs n ∧
      (∀ z ∈ S, z ≠ xs n → z ≠ xs (n + 1) → MonochromaticallyReaches D color z (xs (n + 1))) ∧
      ¬ MonochromaticallyReaches D color (xs n) (xs (n + 1)) ∧ D (xs (n + 1)) (xs n) := by
    intro n
    rw [hsucc]
    exact (hs _ (hmem n)).2
  set c := color (xs 1) (xs 0) with hc
  -- all back arcs have colour c
  have hcol : ∀ n, color (xs (n + 1)) (xs n) = c := by
    intro n
    induction n with
    | zero => rfl
    | succ n ihn =>
      by_contra hne
      have h1 := hS n
      have h2 := hS (n + 1)
      have hD2 : D (xs (n + 2)) (xs (n + 1)) := h2.2.2.2
      have hD1 : D (xs (n + 1)) (xs n) := h1.2.2.2
      by_cases heq : xs n = xs (n + 2)
      · apply h1.2.2.1
        rw [heq]
        exact ⟨_, Relation.ReflTransGen.single ⟨hD2, rfl⟩⟩
      · obtain ⟨d, hd⟩ := h2.2.1 (xs n) (hmem n) (fun h => h1.1 h.symm) heq
        rcases Relation.ReflTransGen.cases_head hd with h | ⟨w, ⟨hw, hwd⟩, _⟩
        · exact heq h
        have hd01 := htwo _ _ hw
        rw [hwd] at hd01
        have hc01 := htwo _ _ hD1
        rw [ihn] at hc01
        rcases fin3_two c _ d hc01 (htwo _ _ hD2) hd01 hne with hdc | hdc
        · -- x_{n+1} → x_n ⇝ x_{n+2} in colour c
          apply h2.2.2.1
          refine ⟨c, Relation.ReflTransGen.head ⟨hD1, ihn⟩ ?_⟩
          rw [← hdc]; exact hd
        · -- x_n ⇝ x_{n+2} → x_{n+1} in colour d
          apply h1.2.2.1
          exact ⟨d, Relation.ReflTransGen.tail hd ⟨hD2, hdc.symm⟩⟩
  have hback : ∀ m n, m ≤ n →
      Relation.ReflTransGen (fun x y => D x y ∧ color x y = c) (xs n) (xs m) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact Relation.ReflTransGen.refl
    | succ n _ ihn => exact Relation.ReflTransGen.head ⟨(hS n).2.2.2, hcol n⟩ ihn
  obtain ⟨a, b, hab, habeq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (⟨xs n, hmem n⟩ : S))
  simp only [Subtype.mk.injEq] at habeq
  rcases lt_or_gt_of_ne hab with h | h
  · apply (hS a).2.2.1
    refine ⟨c, ?_⟩
    rw [habeq]; exact hback (a + 1) b h
  · apply (hS b).2.2.1
    refine ⟨c, ?_⟩
    rw [← habeq]; exact hback (b + 1) a h

theorem finset_sink [DecidableEq V] (htournament : IsTournament D)
    (htwo : ∀ u v, D u v → (color u v = 0 ∨ color u v = 1)) :
    ∀ (S : Finset V), S.Nonempty →
      ∃ v ∈ S, ∀ x ∈ S, x ≠ v → MonochromaticallyReaches D color x v :=
  fun S hS => finset_sink' D color Set.univ (fun _ _ _ _ h => (htournament.2 h).1) htwo S
    (Set.subset_univ _) hS

end SSWAux

theorem solution {V : Type u} [Fintype V] [Nonempty V]
    (D : OPG1808.Digraph V) (color : OPG1808.ArcColoring V) (htournament : IsTournament D)
    (htwo : ∀ u v, D u v → (color u v = 0 ∨ color u v = 1)) :
    ∃ v : V, ∀ x : V, x ≠ v → MonochromaticallyReaches D color x v := by
  classical
  obtain ⟨v, -, hv⟩ := SSWAux.finset_sink D color htournament htwo Finset.univ Finset.univ_nonempty
  exact ⟨v, fun x hx => hv x (Finset.mem_univ x) hx⟩
