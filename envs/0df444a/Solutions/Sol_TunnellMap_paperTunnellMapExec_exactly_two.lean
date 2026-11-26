-- Prove2me | solution 1 for TunnellMap.paperTunnellMapExec_exactly_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:13:08.358699+00:00
-- url     : https://prove2.me/submissions/6510940d-06ed-45c0-9a30-e6813dfee0e8

import Definitions.Def_TunnellMap_ComputableDirect
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_FullAssembly
import Definitions.Def_TunnellMap_ComputableFullMap
import Theorems.Thm_TunnellMap_paperTunnellMapExec_eq
import Theorems.Thm_TunnellMap_paperTunnellMap_exactly_two


set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
variable [Fintype (BRep n)] [Fintype (ARep n)]
namespace TunnellMap
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hbalance : Fintype.card (BRep n) = 2 * Fintype.card (ARep n))
    (fallback : AResidual n) (a : ARep n) :
    ∃ p₁ p₂,
      p₁ ≠ p₂ ∧
      paperTunnellMapExec hnpos hsq fallback p₁ = a ∧
      paperTunnellMapExec hnpos hsq fallback p₂ = a ∧
      ∀ p, paperTunnellMapExec hnpos hsq fallback p = a ↔ p = p₁ ∨ p = p₂ := by
  obtain ⟨p₁, p₂, hne, h₁, h₂, hfib⟩ :=
    paperTunnellMap_exactly_two hn hnpos hbalance a
  refine ⟨p₁, p₂, hne, ?_, ?_, ?_⟩
  · rw [paperTunnellMapExec_eq hn hnpos hsq hbalance]; exact h₁
  · rw [paperTunnellMapExec_eq hn hnpos hsq hbalance]; exact h₂
  · intro p
    rw [paperTunnellMapExec_eq hn hnpos hsq hbalance]
    exact hfib p
end TunnellMap
