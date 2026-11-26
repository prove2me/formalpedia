-- Prove2me | solution 1 for SensitivitySocketEventSupport.target_part_card_le_socket_sum
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:25:27.295499+00:00
-- url     : https://prove2.me/submissions/b792414a-72a2-4486-95ac-827d776d5d0b

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivitySocketEventSupport
end SensitivitySocketEventSupport
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates


/-! Actual one-bit support and decomposition of local gate events. -/
open SensitivitySocketEventSupport
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityGuardEvents SensitivityFiniteRanks SensitivityStrictGateStates
set_option autoImplicit false
variable {V S I Color : Type} {L : ℕ}


theorem _root_.solution [Fintype S] [Fintype I]
    (E : Finset ((V × S) × I)) (v : V) :
    (E.filter fun bit => bit.1.1 = v).card ≤
      ∑ s : S, ((Finset.univ : Finset I).filter fun i => ((v,s),i) ∈ E).card := by
  classical
  have hsub : (E.filter fun bit => bit.1.1 = v) ⊆
      (Finset.univ : Finset S).biUnion fun s => (((Finset.univ : Finset I).filter fun i => ((v,s),i) ∈ E).image fun i => ((v,s),i)) := by
    intro bit hbit
    obtain ⟨⟨⟨v', s⟩, i⟩, rfl⟩ : ∃ b, b = bit := ⟨bit, rfl⟩
    simp only [Finset.mem_filter] at hbit
    obtain ⟨hm, hv⟩ := hbit
    subst hv
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_filter]
    exact ⟨s, i, hm, rfl⟩
  exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun s _ => Finset.card_image_le))


