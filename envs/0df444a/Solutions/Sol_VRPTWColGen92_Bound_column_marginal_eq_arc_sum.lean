-- Prove2me | solution 1 for VRPTWColGen92.Bound.column_marginal_eq_arc_sum
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:48:05.209702+00:00
-- url     : https://prove2.me/submissions/c9f23ae4-5ed9-4d76-91a1-1cc9f801780d

import Mathlib
import Definitions.Def_VRPTWColGen92_Bound_Network
import Definitions.Def_VRPTWColGen92_Bound_CoveringLP

set_option autoImplicit false
open VRPTWColGen92.Bound

theorem X_zip_sum {n : ℕ} (F : Fin (n + 1) → Fin (n + 1) → ℝ) (g : Fin (n + 1) → ℝ)
    (p : List (Fin (n + 1))) :
    ∀ (a z : Fin (n + 1)),
    ((((a :: p) ++ [z]).zip (p ++ [z])).map (fun e => F e.1 e.2 - g e.1)).sum =
      ((((a :: p) ++ [z]).zip (p ++ [z])).map (fun e => F e.1 e.2)).sum - (g a + (p.map g).sum) := by
  induction p with
  | nil => intro a z; simp
  | cons x p' ih =>
    intro a z
    have := ih x z
    simp only [List.cons_append, List.zip_cons_cons, List.map_cons, List.sum_cons] at this ⊢
    rw [this]
    ring

theorem X_count_sum {n : ℕ} (π : Fin (n + 1) → ℝ) (p : List (Fin (n + 1)))
    (hp : (0 : Fin (n + 1)) ∉ p) :
    ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), π i * (p.count i : ℝ) = (p.map π).sum := by
  induction p with
  | nil => simp
  | cons x p' ih =>
    have hx : x ≠ 0 := fun h => hp (h ▸ List.mem_cons_self)
    have hp' : (0 : Fin (n + 1)) ∉ p' := fun h => hp (List.mem_cons_of_mem _ h)
    have h1 : ∀ i : Fin (n + 1), π i * (((x :: p').count i : ℕ) : ℝ) =
        π i * (p'.count i : ℝ) + (if x = i then π i else 0) := by
      intro i
      rw [List.count_cons]
      by_cases hxi : x = i
      · simp [hxi]; ring
      · simp [hxi]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib, ih hp']
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_erase, hx, add_comm]

theorem solution {n : ℕ} (I : Instance n) (y : DualPoint n)
    (p : List (Fin (n + 1))) (hp : (0 : Fin (n + 1)) ∉ p) :
    columnMarginal I y p = pathMarginal I y p := by
  have hnd : (p.map (nodeDual y)).sum = (p.map y.π).sum := by
    congr 1
    apply List.map_congr_left
    intro i hi
    have : i ≠ 0 := fun h => hp (h ▸ hi)
    simp [nodeDual, this]
  have hcost : cost I p = arcSum I.c p := rfl
  have key := X_zip_sum (fun i j => (1 - y.πc) * I.c i j) (nodeDual y) p 0 0
  have hmul : ((((0 :: p) ++ [0]).zip (p ++ [0])).map (fun e : Fin (n + 1) × Fin (n + 1) => (1 - y.πc) * I.c e.1 e.2)).sum
      = (1 - y.πc) * cost I p := by
    rw [hcost, arcSum]
    simp only [nodes]
    rw [← List.sum_map_mul_left]
    simp
  unfold columnMarginal pathMarginal arcSum
  have h2 : (((nodes p).zip (nodes p).tail).map (fun e : Fin (n + 1) × Fin (n + 1) => arcMarginal I y e.1 e.2)) =
      (((0 :: p) ++ [0]).zip (p ++ [0])).map (fun e : Fin (n + 1) × Fin (n + 1) => (1 - y.πc) * I.c e.1 e.2 - nodeDual y e.1) := by
    simp [nodes, arcMarginal]
  rw [h2, key, hmul, hnd, X_count_sum y.π p hp]
  simp [nodeDual]
  ring
