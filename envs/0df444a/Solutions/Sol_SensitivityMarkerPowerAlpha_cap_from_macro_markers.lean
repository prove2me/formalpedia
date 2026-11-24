-- Prove2me | solution 1 for SensitivityMarkerPowerAlpha.cap_from_macro_markers
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:20:27.655695+00:00
-- url     : https://prove2.me/submissions/4f0fcac4-c9a6-4b35-8828-f4fd58ea4834

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkerClusterCaps
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SensitivityClusterPartitionBound
end SensitivityClusterPartitionBound
namespace SensitivityMarkerClusterCaps
end SensitivityMarkerClusterCaps
namespace SensitivityMarkerClusterCounts
end SensitivityMarkerClusterCounts
namespace SensitivityMarkerPowerAlpha
end SensitivityMarkerPowerAlpha


/-! Exact finite partition formulas for the source's summed marker capacities. -/
open SensitivityMarkerPowerAlpha
open scoped Classical BigOperators
open SensitivityMarkerClusterCounts SensitivityMarkerClusterCaps SensitivityClusterPartitionBound
set_option autoImplicit false
variable {V M W : Type} [DecidableEq V] [DecidableEq M]

theorem solution (selected : Finset V) (group : V → M)
    (hselected : selected.Nonempty) (candidates : Finset W) (dominates : M → W → Prop)
    (b1 b2 b3 : ℕ)
    (hdom : ∀ marker ∈ selected, ∀ v ∈ candidates, dominates (group marker) v)
    (hone : ∀ p, (∀ v ∈ candidates, dominates p v) → candidates.card ≤ b1)
    (htwo : ∀ p q, p ≠ q → (∀ v ∈ candidates, dominates p v ∧ dominates q v) → candidates.card ≤ b2)
    (hthree : ∀ p q r, p ≠ q → p ≠ r → q ≠ r →
      (∀ v ∈ candidates, dominates p v ∧ dominates q v ∧ dominates r v) → candidates.card ≤ b3) :
    candidates.card ≤ markerCap b1 b2 b3 group selected := by
  have hd : ∀ p ∈ selected.image group, ∀ v ∈ candidates, dominates p v := by
    intro p hp v hv
    obtain ⟨marker, hm, rfl⟩ := Finset.mem_image.mp hp
    exact hdom marker hm v hv
  unfold markerCap
  split_ifs with h1 h2
  · obtain ⟨marker, hm⟩ := hselected
    exact hone (group marker) (hdom marker hm)
  · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (show 1 < (selected.image group).card by omega)
    exact htwo p q hpq (fun v hv => ⟨hd p hp v hv, hd q hq v hv⟩)
  · obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ :=
      Finset.two_lt_card.mp (show 2 < (selected.image group).card by omega)
    exact hthree p q r hpq hpr hqr (fun v hv => ⟨hd p hp v hv, hd q hq v hv, hd r hr v hv⟩)
