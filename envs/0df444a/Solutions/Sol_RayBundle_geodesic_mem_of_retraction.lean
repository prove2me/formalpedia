-- Prove2me | solution 1 for RayBundle.geodesic_mem_of_retraction
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-10-08T18:57:00.792078+00:00
-- url     : https://prove2.me/submissions/c8d03046-01bd-4d7c-81af-e927c1049cd0

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic

-- Source: RayBundle.Thm_Cayley_geodesic_mem_of_retraction
namespace RayBundle

end RayBundle

open RayBundle
universe u
/-- A retraction that contracts every edge and collapses every edge leaving
its image makes that image convex for all shortest walks. -/
theorem solution {V : Type*} {X : SimpleGraph V}
    (hX : X.Connected) (L : Set V) (r : V → V)
    (hfix : ∀ v ∈ L, r v = v)
    (hstep : ∀ {a b}, X.Adj a b → X.dist (r a) (r b) ≤ 1)
    (hexit : ∀ {a b}, a ∈ L → b ∉ L → X.Adj a b → r b = a)
    {a b : V} (w : X.Walk a b) (hw : w.length = X.dist a b)
    (ha : a ∈ L) (hb : b ∈ L) : ∀ v ∈ w.support, v ∈ L := by
  have hbound : ∀ {a b : V} (w : X.Walk a b), X.dist (r a) (r b) ≤ w.length := by
    intro a b w
    induction w with
    | nil => simp
    | @cons a b c hab w ih =>
        have ht : X.dist (r a) (r c) ≤ X.dist (r a) (r b) + X.dist (r b) (r c) := hX.dist_triangle
        have hs := hstep hab
        simp only [SimpleGraph.Walk.length_cons]
        omega
  induction w with
  | nil => simpa using ha
  | @cons a b c hab w ih =>
      have hbin : b ∈ L := by
        by_contra hbo
        have hle := hbound w
        rw [hexit ha hbo hab, hfix c hb] at hle
        simp only [SimpleGraph.Walk.length_cons] at hw
        omega
      have hw' : w.length = X.dist b c := by
        have ht : X.dist a c ≤ X.dist a b + X.dist b c := hX.dist_triangle
        have hab' : X.dist a b ≤ 1 := by
          simpa using SimpleGraph.dist_le (SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil)
        have hle := SimpleGraph.dist_le w
        simp only [SimpleGraph.Walk.length_cons] at hw
        omega
      intro v hv
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact ha
      · exact ih hw' hbin hb v hv

namespace RayBundle


end RayBundle
