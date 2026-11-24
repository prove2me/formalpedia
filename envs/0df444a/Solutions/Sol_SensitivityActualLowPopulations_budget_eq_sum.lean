-- Prove2me | solution 1 for SensitivityActualLowPopulations.budget_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:19:36.651336+00:00
-- url     : https://prove2.me/submissions/bbaa2287-9e80-4b58-bd60-730e4df8d74a

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActualLowPopulations
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PairedPopulationConstraints
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityActualLowPopulations
end SensitivityActualLowPopulations
namespace SensitivityOperativeHeads
end SensitivityOperativeHeads
namespace SensitivityPairedPopulation
end SensitivityPairedPopulation
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction

section


/-! The four integer population variables are exact counts of actual
operative low rows. Their prefixes and spent budgets equal the sets and
finite sums used by the semantic graph inequalities. -/
namespace SensitivityActualLowPopulations

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityOperativeHeads SensitivityPairedPopulation
set_option autoImplicit false

variable {V S I Color : Type} {L : ℕ}





theorem budget_eq_range_sum (candidates : Finset V) (count : V → ℕ) (q : Fin 4) :
    budget (population candidates count) q =
      ∑ k ∈ Finset.range (q.val+1), k * (candidates.filter fun v => count v = k).card := by
  fin_cases q <;> simp [budget,population,Finset.sum_range_succ]

theorem prefix_filter_eq (candidates : Finset V) (count : V → ℕ) (q k : ℕ) (hk : k ≤ q) :
    (candidates.filter fun v => count v ≤ q).filter (fun v => count v = k) =
      candidates.filter (fun v => count v = k) := by
  ext v
  simp only [Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨hv,hc⟩
    exact ⟨⟨hv,hc ▸ hk⟩,hc⟩


















end
end SensitivityActualLowPopulations

end

/-! The four integer population variables are exact counts of actual
operative low rows. Their prefixes and spent budgets equal the sets and
finite sums used by the semantic graph inequalities. -/
open SensitivityActualLowPopulations
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityOperativeHeads SensitivityPairedPopulation
set_option autoImplicit false
variable {V S I Color : Type} {L : ℕ}

theorem solution (candidates : Finset V) (count : V → ℕ) (q : Fin 4) :
    budget (population candidates count) q =
      ∑ v ∈ candidates.filter (fun v => count v ≤ q.val), count v := by
  rw [budget_eq_range_sum]
  symm
  calc
    (∑ v ∈ candidates.filter (fun v => count v ≤ q.val), count v) =
      ∑ k ∈ Finset.range (q.val+1),
        ∑ v ∈ (candidates.filter fun v => count v ≤ q.val).filter (fun v => count v = k), k := by
      exact (Finset.sum_fiberwise_of_maps_to'
        (fun v hv => Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_filter.mp hv).2))
        (fun k => k)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [prefix_filter_eq candidates count q.val k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
      simp [Nat.mul_comm]
