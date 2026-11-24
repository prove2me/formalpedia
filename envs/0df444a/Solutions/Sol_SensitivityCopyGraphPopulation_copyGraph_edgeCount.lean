-- Prove2me | solution 1 for SensitivityCopyGraphPopulation.copyGraph_edgeCount
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:19:40.513812+00:00
-- url     : https://prove2.me/submissions/4f4f92bf-b5ba-45e7-9196-e8a23710997e

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_CopyGraphPopulation
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_GraphPopulationBounds
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Fin
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace SensitivityActiveSocketPopulation
end SensitivityActiveSocketPopulation
namespace SensitivityCopyGraphPopulation
end SensitivityCopyGraphPopulation
namespace SensitivityGraphPopulation
end SensitivityGraphPopulation
namespace SimpleGraph
end SimpleGraph

section


/-! The quadratic population inequality from an actual independence cap. -/

namespace SensitivityGraphPopulation

noncomputable section
open scoped Classical
open SimpleGraph
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {V : Type} [Fintype V]



theorem edgeFinset_card_eq (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeFinset.card = edgeCount G := by
  simp only [edgeFinset, Set.toFinset_card, edgeCount, Nat.card_eq_fintype_card]











end
end SensitivityGraphPopulation

end

section


/-! Disjoint copies of induced conflict graphs, with exact integral edge bounds. -/
namespace SensitivityCopyGraphPopulation

noncomputable section
open scoped Classical BigOperators
open SensitivityGraphPopulation SensitivityActiveSocketPopulation
set_option autoImplicit false

variable {C V : Type} [Fintype C]









theorem copyGraph_degree (G : SimpleGraph V) (sets : C → Finset V)
    (a : CopyVertex sets) :
    (copyGraph G sets).degree a =
      (G.induce (↑(sets a.1) : Set V)).degree a.2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun b hb =>
    (⟨b.2.val, ((((copyGraph G sets).mem_neighborFinset a b).mp hb).1).symm ▸ b.2.property⟩ :
      {v // v ∈ sets a.1}))
  · intro b hb
    apply ((G.induce (↑(sets a.1) : Set V)).mem_neighborFinset _ _).mpr
    exact (((copyGraph G sets).mem_neighborFinset a b).mp hb).2
  · intro b hb d hd heq
    have hbc := (((copyGraph G sets).mem_neighborFinset a b).mp hb).1
    have hdc := (((copyGraph G sets).mem_neighborFinset a d).mp hd).1
    obtain ⟨cb, vb⟩ := b
    obtain ⟨cd, vd⟩ := d
    dsimp at hbc hdc heq
    subst cb
    subst cd
    exact congrArg (Sigma.mk a.1) (Subtype.ext (congrArg Subtype.val heq))
  · intro v hv
    refine ⟨⟨a.1, v⟩, ?_, rfl⟩
    apply ((copyGraph G sets).mem_neighborFinset _ _).mpr
    exact ⟨rfl, ((G.induce (↑(sets a.1) : Set V)).mem_neighborFinset _ _).mp hv⟩














end
end SensitivityCopyGraphPopulation

end

/-! Disjoint copies of induced conflict graphs, with exact integral edge bounds. -/
open SensitivityCopyGraphPopulation
open scoped Classical BigOperators
open SensitivityGraphPopulation SensitivityActiveSocketPopulation
set_option autoImplicit false
variable {C V : Type} [Fintype C]

theorem solution (G : SimpleGraph V) (sets : C → Finset V) :
    edgeCount (copyGraph G sets) =
      ∑ c, edgeCount (G.induce (↑(sets c) : Set V)) := by
  have htotal := (copyGraph G sets).sum_degrees_eq_twice_card_edges
  simp only [edgeFinset_card_eq] at htotal
  have hsum : (∑ a : CopyVertex sets, (copyGraph G sets).degree a) =
      2 * ∑ c, edgeCount (G.induce (↑(sets c) : Set V)) := by
    simp only [copyGraph_degree, CopyVertex, Fintype.sum_sigma]
    have hlocal : ∀ c, (∑ v : {v // v ∈ sets c},
        (G.induce (↑(sets c) : Set V)).degree v) =
        2 * edgeCount (G.induce (↑(sets c) : Set V)) := by
      intro c
      have h := @SimpleGraph.sum_degrees_eq_twice_card_edges {v // v ∈ sets c}
        (G.induce (↑(sets c) : Set V)) (inferInstance : Fintype {v // v ∈ sets c})
        (inferInstance : DecidableRel (G.induce (↑(sets c) : Set V)).Adj)
      simpa only [edgeFinset_card_eq] using h
    simp_rw [hlocal]
    exact (Finset.mul_sum _ _ _).symm
  omega
