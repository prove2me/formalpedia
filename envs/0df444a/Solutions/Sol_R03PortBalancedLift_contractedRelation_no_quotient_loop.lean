-- Prove2me | solution 1 for R03PortBalancedLift.contractedRelation_no_quotient_loop
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:34:58.295016+00:00
-- url     : https://prove2.me/submissions/2b62ca29-14d9-479a-895a-5ba9244bb3de

import Mathlib
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_2164cbfb81_sp05_port_balanced_quotient_lift_formalization_v

namespace R03PortBalancedLift

open CubicP3Partition

universe u v

variable {P : Type u} {V : Type v} [Fintype P] [Fintype V]

noncomputable section
open scoped Classical

/-- A port-labelled relation on the quotient vertices.  A relation edge records
which endpoint/port of each paired quotient vertex is used. -/
lemma contractedRelation_symm (G : SimpleGraph V)
    (pair : (P × Fin 2) ≃ V) {p q : P} {i j : Fin 2} :
    contractedRelation G pair p i q j ↔
      contractedRelation G pair q j p i := by
  constructor
  · intro h
    exact ⟨h.1.symm, (G.adj_comm _ _).mp h.2⟩
  · intro h
    exact ⟨h.1.symm, (G.adj_comm _ _).mp h.2⟩


end
end R03PortBalancedLift

open R03PortBalancedLift
open CubicP3Partition
universe u v
variable {P : Type u} {V : Type v} [Fintype P] [Fintype V]
open scoped Classical
theorem solution (G : SimpleGraph V)
    (pair : (P × Fin 2) ≃ V) (p : P) (i j : Fin 2) :
    ¬ contractedRelation G pair p i p j := by
  intro h
  exact h.1 rfl

