-- Prove2me | solution 1 for TunnellMap.direct_images_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:04.785633+00:00
-- url     : https://prove2.me/submissions/fb9cee55-8f30-4218-ac16-a2a2b74842ed

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
import Theorems.Thm_TunnellMap_odd_y_of_aRep

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hn : Odd n) (p : ARep n) :
    ¬ (ImagePredicate1 p ∧ ImagePredicate2 p) ∧
      ¬ (ImagePredicate1 p ∧ ImagePredicate3 p) ∧
      ¬ (ImagePredicate2 p ∧ ImagePredicate3 p) := by
  have hy := odd_y_of_aRep hn p
  rcases hy with ⟨ky, hky⟩
  constructor
  · rintro ⟨⟨q₁, hq₁, h₁⟩, ⟨q₂, hq₂, h₂⟩⟩
    rcases hq₁ with ⟨k₁, hk₁⟩
    rcases hq₂ with ⟨k₂, hk₂⟩
    omega
  · constructor
    · rintro ⟨⟨q₁, hq₁, h₁⟩, ⟨q₃, hq₃, h₃⟩⟩
      rcases hq₁ with ⟨k₁, hk₁⟩
      rcases hq₃ with ⟨k₃, hk₃⟩
      omega
    · rintro ⟨⟨q₂, hq₂, h₂⟩, ⟨q₃, hq₃, h₃⟩⟩
      rcases hq₂ with ⟨k₂, hk₂⟩
      rcases hq₃ with ⟨k₃, hk₃⟩
      omega
end TunnellMap
