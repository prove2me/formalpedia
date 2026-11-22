-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.toward_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:06:49.315097+00:00
-- url     : https://prove2.me/submissions/fdded220-e5b3-4871-820c-7374303743c5

module
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_dir_ne_zero
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_mem_points_of_side_eq_zero

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (Pl : Set (K × K)) (hopen : OpenAlong Pl) (L : Dim K)
    (hL : L.zero ≠ L.one) {P : K × K} (hP : P ∈ Pl) (hPL : P ∉ L.points) :
    Function.Injective (toward Pl L P) := by
  intro t t' h
  obtain ⟨r, hr, hX⟩ := hopen ⟨P, L.pt t⟩ hP
  have hmem : (Dim.mk P (L.pt t)).pt r ∈ toward Pl L P t' := by
    rw [← h]
    exact ⟨⟨r, rfl⟩, hX⟩
  obtain ⟨⟨r', hr'⟩, -⟩ := hmem
  have e1 := congrArg Prod.fst hr'
  have e2 := congrArg Prod.snd hr'
  simp only [Dim.pt] at e1 e2
  have hside : L.side P ≠ 0 := fun h0 => hPL (L.mem_points_of_side_eq_zero hL P h0)
  simp only [Dim.side, cross, Dim.dir] at hside
  have hrr : r = r' := by
    have h0 : (r - r') * ((L.one.1 - L.zero.1) * (P.2 - L.zero.2)
        - (L.one.2 - L.zero.2) * (P.1 - L.zero.1)) = 0 := by
      linear_combination (L.one.1 - L.zero.1) * e2 - (L.one.2 - L.zero.2) * e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hside)
  rw [← hrr] at e1 e2
  have h1 : r * (t - t') * (L.one.1 - L.zero.1) = 0 := by linear_combination -e1
  have h2 : r * (t - t') * (L.one.2 - L.zero.2) = 0 := by linear_combination -e2
  by_contra hne
  have hrt : r * (t - t') ≠ 0 := mul_ne_zero hr (sub_ne_zero.mpr hne)
  exact L.dir_ne_zero hL
    (Prod.ext ((mul_eq_zero.mp h1).resolve_left hrt) ((mul_eq_zero.mp h2).resolve_left hrt))
end ParallelPostulate.HyperbolicPlane
