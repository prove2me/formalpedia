-- Prove2me | solution 1 for SimpleGraph.isClique_fromEdgeSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:00:36.037034+00:00
-- url     : https://prove2.me/submissions/a3c383ee-5155-47fc-89ae-4da61e3b16d5

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_RandomGraph
public import Theorems.Thm_Finset_mem_pairs

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V]
namespace SimpleGraph
theorem _root_.solution {A : Finset (Sym2 V)} {s : Finset V} :
    (fromEdgeSet (A : Set (Sym2 V))).IsClique (s : Set V) ↔ s.pairs ⊆ A := by
  constructor
  · intro h e he
    induction e using Sym2.ind with
    | _ v w =>
      obtain ⟨hv, hw, hvw⟩ := mem_pairs.mp he
      exact (fromEdgeSet_adj _).mp (h hv hw hvw) |>.1
  · intro h v hv w hw hvw
    exact (fromEdgeSet_adj _).mpr ⟨h (mem_pairs.mpr ⟨hv, hw, hvw⟩), hvw⟩
end SimpleGraph
