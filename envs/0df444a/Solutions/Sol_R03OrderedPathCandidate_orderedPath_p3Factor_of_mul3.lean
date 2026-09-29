-- Prove2me | solution 1 for R03OrderedPathCandidate.orderedPath_p3Factor_of_mul3
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:34:57.086596+00:00
-- url     : https://prove2.me/submissions/fa220dcb-0076-4225-bb8e-b2c31128f738

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_f0a6fd554c_ordered_path_p3factor_candidate_v1

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace R03OrderedPathCandidate

open CubicP3Partition

universe u
variable {V : Type u}

/-- A spanning ordered path, with consecutive vertices joined by graph edges. -/
lemma idx3_eq_finProd (k : Nat) (i : Fin k) (j : Fin 3) :
    (finProdFinEquiv (i, j) : Fin (k * 3)) = idx3 k i j := by
  simp [finProdFinEquiv, idx3, Nat.mul_comm]


end R03OrderedPathCandidate

open R03OrderedPathCandidate
open CubicP3Partition
universe u
variable {V : Type u}
theorem solution
    {k : Nat} {G : SimpleGraph V} (p : OrderedPath G (k * 3)) :
    Nonempty (P3Factor G) := by
  classical
  refine ⟨{
    blockCount := k
    place := finProdFinEquiv.trans p.place
    edge01 := ?_
    edge12 := ?_ }⟩
  · intro i
    have h := p.edge ⟨i.val * 3, by omega⟩
    simpa [idx3, finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using h
  · intro i
    have h := p.edge ⟨i.val * 3 + 1, by omega⟩
    have hi : (finProdFinEquiv (i, (1 : Fin 3)) : Fin (k * 3)) =
        ⟨i.val * 3 + 1, by omega⟩ := by
      ext
      simp [finProdFinEquiv]
      omega
    have hi' : (finProdFinEquiv (i, (2 : Fin 3)) : Fin (k * 3)) =
        ⟨i.val * 3 + 2, by omega⟩ := by
      ext
      simp [finProdFinEquiv]
      omega
    change G.Adj (p.place (finProdFinEquiv (i, (1 : Fin 3))))
      (p.place (finProdFinEquiv (i, (2 : Fin 3))))
    rw [hi, hi']
    exact h
