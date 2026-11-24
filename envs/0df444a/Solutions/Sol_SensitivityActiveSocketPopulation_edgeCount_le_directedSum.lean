-- Prove2me | solution 1 for SensitivityActiveSocketPopulation.edgeCount_le_directedSum
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:19:32.580804+00:00
-- url     : https://prove2.me/submissions/d8ab48eb-7751-46c6-8829-ff5f959edd60

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_GraphPopulationBounds
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PseudoforestCover
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

namespace SensitivityActiveSocketGeometry
end SensitivityActiveSocketGeometry
namespace SensitivityActiveSocketPopulation
end SensitivityActiveSocketPopulation
namespace SensitivityGraphPopulation
end SensitivityGraphPopulation
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityPseudoforest
end SensitivityPseudoforest
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
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


/-!
Three independent palettes for a finite orientation of outdegree at most one.
Sinks receive two colors, all other vertices one. This directly gives the
population-plus-sinks inequality without classifying connected components.
-/

namespace SensitivityPseudoforest

noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false

variable {V : Type}












theorem sum_outgoing_eq_incoming (R : V → V → Prop) (s : Finset V) :
    ∑ v ∈ s, (outgoing R s v).card = ∑ v ∈ s, (incoming R s v).card := by
  simp only [outgoing, incoming, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm



theorem neighbors_card_le (R : V → V → Prop) (s : Finset V) (v : V) :
    (neighbors R s v).card ≤ (outgoing R s v).card + (incoming R s v).card := by
  have heq : neighbors R s v = outgoing R s v ∪ incoming R s v := by
    ext w
    simp only [neighbors, outgoing, incoming, Finset.mem_filter, Finset.mem_union]
    tauto
  rw [heq]
  exact Finset.card_union_le _ _














end
end SensitivityPseudoforest

end

/-! Population inequalities with actual positive-socket and guard-count premises. -/
open SensitivityActiveSocketPopulation
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityActiveSocketGeometry SensitivityGraphPopulation SensitivityPseudoforest
set_option autoImplicit false
variable {V M B I Color : Type} {L : ℕ}

theorem solution [Fintype V] (G : SimpleGraph V)
    (D : V → V → Prop) (hcover : ∀ v w, G.Adj v w → D v w ∨ D w v) :
    edgeCount G ≤ ∑ v : V, (outgoing D Finset.univ v).card := by
  have hdegree : ∀ v, G.degree v ≤
      (outgoing D Finset.univ v).card + (incoming D Finset.univ v).card := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply (Finset.card_le_card ?_).trans (neighbors_card_le D Finset.univ v)
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hcover v w ((G.mem_neighborFinset v w).mp hw)⟩
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hdegree v)
  rw [Finset.sum_add_distrib, ← sum_outgoing_eq_incoming D Finset.univ] at hsum
  have hdegreeSum := G.sum_degrees_eq_twice_card_edges
  simp only [edgeFinset_card_eq] at hdegreeSum
  rw [hdegreeSum] at hsum
  omega
