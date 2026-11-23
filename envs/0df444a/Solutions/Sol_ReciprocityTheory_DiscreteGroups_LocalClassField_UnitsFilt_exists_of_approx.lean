-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.exists_of_approx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:48.250243+00:00
-- url     : https://prove2.me/submissions/f0e00d9f-1acb-4c01-a9f4-58eb1dabb4e4

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
open Finset
variable {U : Type*} [CommGroup U]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
theorem _root_.solution (V : ℕ → Subgroup U)
    (hcomp : ∀ v : ℕ → U, (∀ k, v k ∈ V k) → ∃ s ∈ V 0, ∀ n, s / ∏ k ∈ range n, v k ∈ V n)
    (hsep : ∀ u, (∀ n, u ∈ V n) → u = 1) (Z : Subgroup U) (f : U →* U)
    (hfV : ∀ n, ∀ u ∈ V n, f u ∈ V n) (hfZ : ∀ u, f u ∈ Z)
    (step : ∀ n, ∀ u ∈ V n, u ∈ Z → ∃ v ∈ V n, u / f v ∈ V (n + 1)) :
    ∀ u ∈ V 0, u ∈ Z → ∃ v ∈ V 0, f v = u := by
  classical
  intro u hu hZ
  choose! c hc using step
  let w : ℕ → U := fun n => Nat.rec u (fun n x => x / f (c n x)) n
  have hw : ∀ n, w n ∈ V n ∧ w n ∈ Z := by
    intro n
    induction n with
    | zero => exact ⟨hu, hZ⟩
    | succ n ih => exact ⟨(hc n _ ih.1 ih.2).2, Z.div_mem ih.2 (hfZ _)⟩
  have hprod : ∀ n, w n = u / f (∏ k ∈ range n, c k (w k)) := by
    intro n
    induction n with
    | zero => simp [w]
    | succ n ih =>
      rw [prod_range_succ, map_mul, ← div_div, ← ih]
  obtain ⟨s, hs0, hs⟩ := hcomp (fun k => c k (w k)) (fun k => (hc k _ (hw k).1 (hw k).2).1)
  refine ⟨s, hs0, ?_⟩
  have h1 : u / f s = 1 := hsep _ fun n => by
    have h2 : u / f s = w n / f (s / ∏ k ∈ range n, c k (w k)) := by
      rw [hprod n, map_div, div_div_div_cancel_right]
    rw [h2]
    exact (V n).div_mem (hw n).1 (hfV n _ (hs n))
  exact (div_eq_one.1 h1).symm
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
