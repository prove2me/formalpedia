-- Prove2me | solution 1 for Problem97.CGN.CGN4g2_consecutiveTurn_nonpos_of_capBlock
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T05:49:26.770523+00:00
-- url     : https://prove2.me/submissions/805f4f38-054e-48ad-a613-64c152e5bb89

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN4g:26998:28507. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_CGN_CGN4g
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin

section Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN4g

open Problem97 Problem97.CGN

/- Fragment from Erdos9796Proof.P97.CGN.CGN4g; source SHA-256 c412b95ca627805e0db3a1f0d192f80b93891249e4eb1369844d4f8206dcba79 -/


/-!
# CGN4g: ordered-cap block packaging

This file adds the closure-plan data carrier for the ordered-cap block cut out
of a global convex-boundary enumeration, together with the theorem wrappers
that are pure packaging.

The geometric producers for the block (`CGN4g1`, `CGN4g3`, `CGN4g4`) remain
separate. The declarations here are the sanctioned interfaces consumed by the
existing CGN6 / CGN7 layers.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace












variable {A C : Finset ℝ²}












































theorem solution
    {A C : Finset ℝ²} {n m : ℕ}
    {phi : Fin n → ℝ²} {L : OrderedCap m}
    (Block : BoundaryCapBlock A C phi L)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi i) (phi j) (phi k) < 0) :
    ∀ t : ℕ, ∀ ht : t + 2 < m,
      Problem97.signedArea2
        (L.points ⟨t, by
          exact lt_trans
            (Nat.lt_add_of_pos_right (by decide : 0 < (2 : ℕ))) ht⟩)
        (L.points ⟨t + 1, by
          exact lt_trans
            (Nat.succ_lt_succ (Nat.lt_add_of_pos_right (by decide : 0 < (1 : ℕ))))
            ht⟩)
        (L.points ⟨t + 2, by
          exact ht⟩) ≤ 0 := by
  intro t ht
  let i0 : Fin m := ⟨t, by
    exact lt_trans
      (Nat.lt_add_of_pos_right (by decide : 0 < (2 : ℕ))) ht⟩
  let i1 : Fin m := ⟨t + 1, by
    exact lt_trans
      (Nat.succ_lt_succ (Nat.lt_add_of_pos_right (by decide : 0 < (1 : ℕ))))
      ht⟩
  let i2 : Fin m := ⟨t + 2, ht⟩
  have hi01 : i0 < i1 := by
    change t < t + 1
    omega
  have hi12 : i1 < i2 := by
    change t + 1 < t + 2
    omega
  have hidx01 : Block.idx i0 < Block.idx i1 := Block.idx_strict hi01
  have hidx12 : Block.idx i1 < Block.idx i2 := Block.idx_strict hi12
  exact le_of_lt <| by
    simpa [i0, i1, i2, Block.points_eq] using hneg hidx01 hidx12

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN4g
