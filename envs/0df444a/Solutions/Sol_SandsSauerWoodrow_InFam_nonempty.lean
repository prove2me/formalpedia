-- Prove2me | solution 1 for SandsSauerWoodrow.InFam_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-17T23:27:46.416621+00:00
-- url     : https://prove2.me/submissions/7d8a7de2-8ede-4572-99e5-59d13a7167da

import Definitions.Def_opg1808_colored_tournaments
import Definitions.Def_SandsSauerWoodrow_OrderOnSets
import Definitions.Def_SandsSauerWoodrow_NoInfinitePath

open OPG1808
open SandsSauerWoodrow

universe u

private lemma rc_refl {V : Type u} (D : Digraph V) (color : ArcColoring V) (k : Fin 3) (x : V) :
    ReachC D color k x x := Relation.ReflTransGen.refl

private lemma rc_trans {V : Type u} {D : Digraph V} {color : ArcColoring V} {k : Fin 3}
    {x y z : V} (h1 : ReachC D color k x y) (h2 : ReachC D color k y z) :
    ReachC D color k x z := Relation.ReflTransGen.trans h1 h2

/-- Some vertex has no red successor from which it is not red-reachable, else choosing such a
successor repeatedly builds an infinite outward path for the asymmetric part of red
reachability. Then that vertex's singleton is in the family. -/
theorem solution {V : Type u} [Nonempty V] (D : Digraph V) (color : ArcColoring V)
    (hA2 : NoInfinitePath (asymPart D color 0)) :
    ∃ v : V, InFam D color ({v} : Set V) := by
  classical
  have hu : ∃ v : V, ∀ y : V, ReachC D color 0 v y → ReachC D color 0 y v := by
    by_contra h
    push_neg at h
    let g : V → V := fun v => Classical.choose (h v)
    have hg : ∀ v : V, ReachC D color 0 v (g v) ∧ ¬ ReachC D color 0 (g v) v :=
      fun v => Classical.choose_spec (h v)
    let f : ℕ → V := fun n => Nat.rec (Classical.arbitrary V) (fun _ v => g v) n
    have hfs : ∀ n : ℕ, f (n + 1) = g (f n) := fun _ => rfl
    have hstep : ∀ n : ℕ, asymPart D color 0 (f n) (f (n + 1)) := by
      intro n
      have h1 : ReachC D color 0 (f n) (g (f n)) := (hg (f n)).1
      have h2 : ¬ ReachC D color 0 (g (f n)) (f n) := (hg (f n)).2
      simpa [asymPart, hfs] using ⟨h1, h2⟩
    have hreach : ∀ (i k : ℕ), ReachC D color 0 (f i) (f (i + k)) := by
      intro i k
      induction k with
      | zero => simpa using rc_refl (D := D) (color := color) (k := 0) (f i)
      | succ k ih =>
          have h := rc_trans ih (hstep (i + k)).1
          simpa [Nat.add_assoc] using h
    have hinj : Function.Injective f := by
      intro i j hij
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · obtain ⟨k, hk⟩ : ∃ k, j = i + 1 + k := ⟨j - i - 1, by omega⟩
        have h1 : ReachC D color 0 (f (i + 1)) (f j) := by
          rw [hk]; exact hreach (i + 1) k
        rw [← hij] at h1
        exact (hstep i).2 h1
      · obtain ⟨k, hk⟩ : ∃ k, i = j + 1 + k := ⟨i - j - 1, by omega⟩
        have h1 : ReachC D color 0 (f (j + 1)) (f i) := by
          rw [hk]; exact hreach (j + 1) k
        rw [hij] at h1
        exact (hstep j).2 h1
    exact hA2 ⟨f, hinj, hstep⟩
  obtain ⟨v, hv⟩ := hu
  refine ⟨v, ?_⟩
  refine ⟨⟨v, by simp⟩, ?_, ?_⟩
  · intro x hx y hy hne
    simp only [Set.mem_singleton_iff] at hx hy
    exact absurd (hx.trans hy.symm) hne
  · intro y hy
    obtain ⟨s, hs, hsr⟩ := hy
    rw [Set.mem_singleton_iff] at hs
    exact ⟨v, by simp, 0, hv y (hs ▸ hsr)⟩
