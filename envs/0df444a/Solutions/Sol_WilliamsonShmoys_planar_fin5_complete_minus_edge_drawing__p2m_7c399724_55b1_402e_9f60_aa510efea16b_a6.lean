-- Prove2me | solution 1 for WilliamsonShmoys.planar_fin5_complete_minus_edge_drawing__p2m_7c399724_55b1_402e_9f60_aa510efea16b_a6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T23:04:34.452131+00:00
-- url     : https://prove2.me/submissions/5c5df9f3-64cc-4d03-aed9-2f2ca23c3573

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp

set_option autoImplicit false

def k5Point (u : Fin 5) : ℝ × ℝ :=
  if u.val = 0 then (0, 0) else
  if u.val = 1 then (2, 2) else
  if u.val = 2 then (6, 0) else
  if u.val = 3 then (0, 6) else (1, 1)

def k5Arc (u v : Fin 5) (t : ℝ) : ℝ × ℝ :=
  ((1 - t) * (k5Point u).1 + t * (k5Point v).1,
   (1 - t) * (k5Point u).2 + t * (k5Point v).2)

theorem k5Point_injective : Function.Injective k5Point := by
  intro u v h
  fin_cases u <;> fin_cases v <;> norm_num [k5Point] at h <;> rfl

theorem k5Arc_continuous (u v : Fin 5) : ContinuousOn (k5Arc u v) (Set.Icc 0 1) := by
  fun_prop [k5Arc]

theorem k5Arc_endpoints (u v : Fin 5) : k5Arc u v 0 = k5Point u ∧ k5Arc u v 1 = k5Point v := by
  simp [k5Arc]

theorem k5Arc_no_vertex (u v : Fin 5) (huv : u < v) (hallowed : u ≠ 0 ∨ v ≠ 1)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) (w : Fin 5) : k5Arc u v t ≠ k5Point w := by
  intro heq
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  rcases ht with ⟨ht0, ht1⟩
  fin_cases u <;> fin_cases v <;> norm_num at huv
  all_goals norm_num at hallowed
  all_goals fin_cases w <;> norm_num [k5Arc, k5Point] at hx <;> norm_num [k5Arc, k5Point] at hy <;> linarith

theorem k5Arc_injective (u v : Fin 5) (huv : u < v) :
    Set.InjOn (k5Arc u v) (Set.Icc 0 1) := by
  intro t ht s hs heq
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  fin_cases u <;> fin_cases v <;> norm_num at huv
  all_goals norm_num [k5Arc, k5Point] at hx <;> norm_num [k5Arc, k5Point] at hy <;> linarith

theorem k5Arcs_meet_only_at_endpoints (u v x y : Fin 5)
    (huv : u < v) (hxy : x < y) (hallowed : u ≠ 0 ∨ v ≠ 1) (hallowed' : x ≠ 0 ∨ y ≠ 1)
    (hne : (u, v) ≠ (x, y)) (t s : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (heq : k5Arc u v t = k5Arc x y s) :
    (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) := by
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  rcases ht with ⟨ht0, ht1⟩
  rcases hs with ⟨hs0, hs1⟩
  fin_cases u <;> fin_cases v <;> norm_num at huv
  all_goals norm_num at hallowed
  all_goals fin_cases x <;> fin_cases y <;> norm_num at hxy
  all_goals norm_num at hallowed'
  all_goals norm_num at hne
  all_goals norm_num [k5Arc, k5Point] at hx <;> norm_num [k5Arc, k5Point] at hy
  all_goals constructor <;> (first | left; linarith | right; linarith)


def k5Graph : SimpleGraph (Fin 5) := SimpleGraph.fromRel
  (fun x y : Fin 5 => x ≠ y ∧ (x ≠ 0 ∨ y ≠ 1) ∧ (x ≠ 1 ∨ y ≠ 0))

theorem k5_adj_ne_01 (u v : Fin 5) (h : k5Graph.Adj u v) : u ≠ 0 ∨ v ≠ 1 := by
  simp only [k5Graph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h
  · exact h.2.1
  · exact h.2.2.symm

theorem solution : WilliamsonShmoys.HasPlanarDrawingOn (SimpleGraph.fromRel (fun (x y : Fin 5) => x ≠ y ∧ ((x ≠ 0) ∨ (y ≠ 1)) ∧ ((x ≠ 1) ∨ (y ≠ 0)))) := by
  change WilliamsonShmoys.HasPlanarDrawingOn k5Graph
  refine ⟨k5Point, k5Arc, k5Point_injective, ?_, ?_⟩
  · intro u v huv hadj
    exact ⟨k5Arc_continuous u v, k5Arc_injective u v huv,
      (k5Arc_endpoints u v).1, (k5Arc_endpoints u v).2,
      fun t ht w => k5Arc_no_vertex u v huv (k5_adj_ne_01 u v hadj) t ht w⟩
  · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
    exact k5Arcs_meet_only_at_endpoints u v x y huv hxy
      (k5_adj_ne_01 u v hadj) (k5_adj_ne_01 x y hadj') hne t s ht hs heq

