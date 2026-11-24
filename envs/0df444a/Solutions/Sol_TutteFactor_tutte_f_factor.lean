-- Prove2me | solution 1 for TutteFactor.tutte_f_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:19:16.427991+00:00
-- url     : https://prove2.me/submissions/b927705b-8619-4d4f-ac4f-567ec6114116

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactor
public import Definitions.Def_FFactorLib_Solution
public import Theorems.Thm_FFactor_tutte_f_factor


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open TutteFactor
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace TutteFactor
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℕ) :
    (∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, H ≤ G ∧ ∀ v, H.degree v = f v) ↔
      ∀ S T : Finset V, Disjoint S T →
        (oddCount G f S T : ℤ) ≤ ∑ v ∈ S, (f v : ℤ) - ∑ v ∈ T, (f v : ℤ) +
          ∑ v ∈ T, (#{u ∈ G.neighborFinset v | u ∉ S} : ℤ) :=
  FFactor.tutte_f_factor G f
end TutteFactor
