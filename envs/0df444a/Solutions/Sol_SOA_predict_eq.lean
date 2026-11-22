-- Prove2me | solution 1 for SOA_predict_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:52.649425+00:00
-- url     : https://prove2.me/submissions/1b1a047c-3878-42c7-8bd4-dcf40aaf0d41

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra

set_option autoImplicit true
@[expose] public section
public section
theorem _root_.solution (X : Type) (C : ConceptClass X Bool)
    (history : List (X × Bool)) (x : X) :
    (SOA X C).predict history x =
      if LittlestoneDim X {c ∈ versionSpace C history | c x = true} ≥
         LittlestoneDim X {c ∈ versionSpace C history | c x = false}
      then true else false := rfl
