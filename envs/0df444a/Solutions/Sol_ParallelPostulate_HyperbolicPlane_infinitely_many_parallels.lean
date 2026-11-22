-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.infinitely_many_parallels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:09:23.888358+00:00
-- url     : https://prove2.me/submissions/e8bcf990-b401-4d2b-aceb-d164b894d7b0

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_toward_misses
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_toward_injective

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (Pl : Set (K × K)) (hopen : OpenAlong Pl) (L : Dim K)
    (hL : L.zero ≠ L.one) {P : K × K} (hP : P ∈ Pl) (hPL : P ∉ L.points)
    (hbeyond : {t : K | L.pt t ∉ Pl}.Infinite) : {S | Misses Pl L P S}.Infinite :=
  Set.infinite_of_injOn_mapsTo (toward_injective Pl hopen L hL hP hPL).injOn
    (fun _ ht => toward_misses Pl L hL hP hPL ht) hbeyond
end ParallelPostulate.HyperbolicPlane
