-- Prove2me | solution 1 for OPG1808.order_eleven
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T01:18:49.45387+00:00
-- url     : https://prove2.me/submissions/76bf43f2-02ce-4ef0-b396-22d56fe0dab4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OPG1808_missing_predecessor_cycle_of_no_source
import Theorems.Thm_OPG1808_order_seven
import Theorems.Thm_OPG1808_order_eight_to_eleven_cycle_predecessor_reachable
import Lean.Elab.Tactic.Omega

open OPG1808

universe u

/-- The checked order-seven base case leaves only cycle orders eight through eleven. -/
theorem solution
    {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V)
    (htournament : IsTournament D)
    (horder : Fintype.card V ≤ 11)
    (hnoRainbow : ¬ HasRainbowDirectedTriangle D color) :
    ∃ s : V, IsMonochromaticSource D color s := by
  classical
  by_contra hnosource
  obtain ⟨m, hm, hcard, e, he, hcycle⟩ :=
    OPG1808.missing_predecessor_cycle_of_no_source D color htournament hnosource
  let inst : NeZero m := ⟨by omega⟩
  let D' : Digraph (Fin m) := fun i j ↦ D (e i) (e j)
  let color' : ArcColoring (Fin m) := fun i j ↦ color (e i) (e j)
  have ht' : IsTournament D' := by
    constructor
    · intro i
      exact htournament.1 (e i)
    · intro i j hij
      exact htournament.2 (fun h ↦ hij (he h))
  have hno' : ¬HasRainbowDirectedTriangle D' color' := by
    rintro ⟨a, b, c, hab, hbc, hca, hDab, hDbc, hDca, hCab, hCbc, hCca⟩
    exact hnoRainbow ⟨e a, e b, e c, he.ne hab, he.ne hbc, he.ne hca,
      hDab, hDbc, hDca, hCab, hCbc, hCca⟩
  have hreturn : ∃ i : Fin m, MonochromaticallyReaches D' color' (finRotate m i) i := by
    by_cases hsmall : m ≤ 7
    · obtain ⟨s, hs⟩ := OPG1808.order_seven D' color' ht'
        (by simpa only [Fintype.card_fin] using hsmall) hno'
      obtain ⟨i, hi⟩ := (finRotate m).surjective s
      exact ⟨i, by simpa only [hi] using hs i⟩
    · exact OPG1808.order_eight_to_eleven_cycle_predecessor_reachable
        m (by omega) (hcard.trans horder) D' color' ht' hno'
        (fun i ↦ (hcycle i).1)
  obtain ⟨i, k, hpath⟩ := hreturn
  exact (hcycle i).2 ⟨k, hpath.lift e (fun _ _ h ↦ h)⟩
