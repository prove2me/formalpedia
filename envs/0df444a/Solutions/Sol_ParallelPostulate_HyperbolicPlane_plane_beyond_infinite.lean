-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.plane_beyond_infinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:07:34.725931+00:00
-- url     : https://prove2.me/submissions/6377b4f2-4d13-4b4a-86de-5813a561a8e3

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_plane_beyond

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ : K} (hκ : κ < 0) (L : Dim K) (hL : L.zero ≠ L.one) :
    {t : K | L.pt t ∉ plane κ}.Infinite := by
  obtain ⟨T, hT⟩ := plane_beyond hκ L hL
  exact (Set.Ici_infinite T).mono (fun t ht => hT t ht)
end ParallelPostulate.HyperbolicPlane
