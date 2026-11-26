-- Prove2me | solution 1 for TunnellMap.paperTunnellMapTotal_exactly_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:01:10.229961+00:00
-- url     : https://prove2.me/submissions/fbd4092c-b5d1-4bca-960b-2e121824a866

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
import Theorems.Thm_TunnellMap_paperTunnellMapTotal_eq
import Theorems.Thm_TunnellMap_paperTunnellMap_exactly_two


set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (a : ARep n) :
    ∃ p₁ p₂,
      p₁ ≠ p₂ ∧
      paperTunnellMapTotal hn hnpos hsq hbal p₁ = a ∧
      paperTunnellMapTotal hn hnpos hsq hbal p₂ = a ∧
      ∀ p, paperTunnellMapTotal hn hnpos hsq hbal p = a ↔ p = p₁ ∨ p = p₂ := by
  obtain ⟨p₁, p₂, hne, h₁, h₂, hfib⟩ :=
    paperTunnellMap_exactly_two hn hnpos (fintype_balance_of_nat_card hbal) a
  refine ⟨p₁, p₂, hne, ?_, ?_, ?_⟩
  · rw [paperTunnellMapTotal_eq hn hnpos hsq hbal]; exact h₁
  · rw [paperTunnellMapTotal_eq hn hnpos hsq hbal]; exact h₂
  · intro p
    rw [paperTunnellMapTotal_eq hn hnpos hsq hbal]
    exact hfib p
end TunnellMap
