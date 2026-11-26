-- Prove2me | solution 1 for TunnellMap.direct_domains_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:02.596274+00:00
-- url     : https://prove2.me/submissions/49cdf971-ef03-4639-bb31-c01992754396

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
import Theorems.Thm_TunnellMap_odd_y_of_bOdd

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hn : Odd n) (p : BOddRep n) :
    ¬ (DirectPredicate1 p ∧ DirectPredicate2 p) ∧
      ¬ (DirectPredicate1 p ∧ DirectPredicate3 p) ∧
      ¬ (DirectPredicate2 p ∧ DirectPredicate3 p) := by
  have hy := odd_y_of_bOdd hn p
  rcases hy with ⟨ky, hky⟩
  rcases p.2.2 with ⟨kz, hkz⟩
  constructor
  · rintro ⟨⟨q₁, h₁⟩, ⟨q₂, h₂⟩⟩
    omega
  · constructor
    · rintro ⟨⟨q₁, h₁⟩, ⟨q₃, h₃⟩⟩
      omega
    · rintro ⟨⟨q₂, h₂⟩, ⟨q₃, h₃⟩⟩
      omega
end TunnellMap
