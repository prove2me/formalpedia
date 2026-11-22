-- Prove2me | solution 1 for SOA_update_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:53.184671+00:00
-- url     : https://prove2.me/submissions/0026bb79-23bb-4b3f-9b74-298c554312f7

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra

set_option autoImplicit true
@[expose] public section
public section
theorem _root_.solution (X : Type) (C : ConceptClass X Bool)
    (history : List (X × Bool)) (x : X) (y : Bool) :
    (SOA X C).update history x y = history ++ [(x, y)] := rfl
