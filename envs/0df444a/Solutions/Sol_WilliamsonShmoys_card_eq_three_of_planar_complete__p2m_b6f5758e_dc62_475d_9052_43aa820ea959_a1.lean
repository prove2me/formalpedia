-- Prove2me | solution 1 for WilliamsonShmoys.card_eq_three_of_planar_complete__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-29T22:58:24.199998+00:00
-- url     : https://prove2.me/submissions/5ee45b95-8d7e-4362-a17f-d7b0c06fedc5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp

set_option autoImplicit false

def k4Point (u : Fin 4) : ℝ × ℝ :=
  if u.val = 0 then (0, 0) else
  if u.val = 1 then (4, 0) else
  if u.val = 2 then (0, 4) else (1, 1)

def k4Arc (u v : Fin 4) (t : ℝ) : ℝ × ℝ :=
  ((1 - t) * (k4Point u).1 + t * (k4Point v).1,
   (1 - t) * (k4Point u).2 + t * (k4Point v).2)

theorem k4Point_injective : Function.Injective k4Point := by
  intro u v h
  fin_cases u <;> fin_cases v <;> norm_num [k4Point] at h <;> rfl

theorem k4Arc_continuous (u v : Fin 4) : ContinuousOn (k4Arc u v) (Set.Icc 0 1) := by
  fun_prop [k4Arc]

theorem k4Arc_endpoints (u v : Fin 4) : k4Arc u v 0 = k4Point u ∧ k4Arc u v 1 = k4Point v := by
  simp [k4Arc, Prod.ext_iff]

theorem k4Arc_no_vertex (u v : Fin 4) (huv : u < v) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) (w : Fin 4) :
    k4Arc u v t ≠ k4Point w := by
  intro heq
  have hcoord := congrArg Prod.fst heq
  have hcoord' := congrArg Prod.snd heq
  rcases ht with ⟨ht0, ht1⟩
  fin_cases u <;> fin_cases v <;> norm_num at huv
  all_goals fin_cases w <;> norm_num [k4Arc, k4Point] at hcoord <;> norm_num [k4Arc, k4Point] at hcoord' <;> linarith

theorem k4Arc_injective (u v : Fin 4) (huv : u < v) :
    Set.InjOn (k4Arc u v) (Set.Icc 0 1) := by
  intro t ht s hs heq
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  fin_cases u <;> fin_cases v <;> norm_num at huv
  all_goals norm_num [k4Arc, k4Point] at hx <;> norm_num [k4Arc, k4Point] at hy <;> linarith

theorem k4Arcs_meet_only_at_endpoints (u v x y : Fin 4)
    (huv : u < v) (hxy : x < y) (hne : (u, v) ≠ (x, y))
    (t s : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (heq : k4Arc u v t = k4Arc x y s) :
    (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) := by
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  rcases ht with ⟨ht0, ht1⟩
  rcases hs with ⟨hs0, hs1⟩
  fin_cases u <;> fin_cases v <;> norm_num at huv
  all_goals fin_cases x <;> fin_cases y <;> norm_num at hxy
  all_goals norm_num at hne
  all_goals norm_num [k4Arc, k4Point] at hx <;> norm_num [k4Arc, k4Point] at hy
  all_goals constructor <;> (first | left; linarith | right; linarith)


theorem k4_drawing (H : SimpleGraph (Fin 4)) : WilliamsonShmoys.HasPlanarDrawingOn H := by
  have h_main : WilliamsonShmoys.HasPlanarDrawingOn H := by
    refine' ⟨k4Point, k4Arc, k4Point_injective, ?_, ?_⟩
    · -- Prove the edge properties: continuity, injectivity, endpoints, interior avoidance
      intro u v huv hadj
      have h₁ : ContinuousOn (k4Arc u v) (Set.Icc (0 : ℝ) 1) := k4Arc_continuous u v
      have h₂ : Set.InjOn (k4Arc u v) (Set.Icc (0 : ℝ) 1) := k4Arc_injective u v huv
      have h₃ : k4Arc u v 0 = k4Point u := (k4Arc_endpoints u v).1
      have h₄ : k4Arc u v 1 = k4Point v := (k4Arc_endpoints u v).2
      have h₅ : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w : Fin 4, k4Arc u v t ≠ k4Point w := by
        intro t ht w
        exact k4Arc_no_vertex u v huv t ht w
      exact ⟨h₁, h₂, h₃, h₄, h₅⟩
    · -- Prove the intersection property: distinct edges meet only at endpoints
      intro u v x y huv hxy hadj hadj' hne t ht s hs heq
      have h₁ : (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) :=
        k4Arcs_meet_only_at_endpoints u v x y huv hxy hne t s ht hs heq
      exact h₁
  exact h_main

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hcomplete : ∀ u v : V, u ≠ v → H.Adj u v),
    Fintype.card V = 3) := by
  intro h
  have hcomplete : ∀ u v : Fin 4, u ≠ v → (⊤ : SimpleGraph (Fin 4)).Adj u v := by
    intro u v huv
    simpa using huv
  have hfalse := h (⊤ : SimpleGraph (Fin 4)) (k4_drawing ⊤) (by decide) hcomplete
  norm_num at hfalse

