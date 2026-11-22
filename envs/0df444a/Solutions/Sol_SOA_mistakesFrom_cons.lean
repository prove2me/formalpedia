-- Prove2me | solution 1 for SOA_mistakesFrom_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:33:12.248434+00:00
-- url     : https://prove2.me/submissions/3ab7d2d3-ce63-492c-a0c3-466437a56500

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra

set_option autoImplicit true
@[expose] public section
public section
theorem _root_.solution (X : Type) (C : ConceptClass X Bool)
    (history : List (X × Bool)) (c : X → Bool) (x : X) (xs : List X) :
    (SOA X C).mistakesFrom history c (x :: xs) =
      (if (SOA X C).predict history x ≠ c x then 1 else 0) +
        (SOA X C).mistakesFrom (history ++ [(x, c x)]) c xs := rfl
