-- Prove2me | solution 1 for TunnellMap.lifted_first_coordinates_same_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:50.83349+00:00
-- url     : https://prove2.me/submissions/34a0851b-5315-4370-8674-25a541c02760

import Definitions.Def_TunnellMap_QuarterTurns
import Definitions.Def_TunnellMap_Midpoint
import Theorems.Thm_TunnellMap_odd_sq_eq_one_add_eight_mul
import Theorems.Thm_TunnellMap_even_sq_eq_four_mul
import Theorems.Thm_TunnellMap_odd_y_of_aRep
import Theorems.Thm_TunnellMap_odd_y_of_bOdd


set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hn : Odd n)
    (s : BOddRep n) (t : ARep n) :
    (Even s.1.x ∧ Even t.1.x) ∨ (Odd s.1.x ∧ Odd t.1.x) := by
  have hsy := odd_y_of_bOdd hn s
  have hty := odd_y_of_aRep hn t
  rcases Int.even_or_odd s.1.x with hsx | hsx
  · rcases Int.even_or_odd t.1.x with htx | htx
    · exact Or.inl ⟨hsx, htx⟩
    · exfalso
      obtain ⟨ksx, hsx₂⟩ := even_sq_eq_four_mul hsx
      obtain ⟨ktx, htx₂⟩ := odd_sq_eq_one_add_eight_mul htx
      obtain ⟨ksy, hsy₂⟩ := odd_sq_eq_one_add_eight_mul hsy
      obtain ⟨kty, hty₂⟩ := odd_sq_eq_one_add_eight_mul hty
      have hsform := s.2.1
      have htform := t.2
      change 2 * s.1.x ^ 2 + s.1.y ^ 2 + 8 * s.1.z ^ 2 = n at hsform
      change 2 * t.1.x ^ 2 + t.1.y ^ 2 + 32 * t.1.z ^ 2 = n at htform
      rw [hsx₂, hsy₂] at hsform
      rw [htx₂, hty₂] at htform
      omega
  · rcases Int.even_or_odd t.1.x with htx | htx
    · exfalso
      obtain ⟨ksx, hsx₂⟩ := odd_sq_eq_one_add_eight_mul hsx
      obtain ⟨ktx, htx₂⟩ := even_sq_eq_four_mul htx
      obtain ⟨ksy, hsy₂⟩ := odd_sq_eq_one_add_eight_mul hsy
      obtain ⟨kty, hty₂⟩ := odd_sq_eq_one_add_eight_mul hty
      have hsform := s.2.1
      have htform := t.2
      change 2 * s.1.x ^ 2 + s.1.y ^ 2 + 8 * s.1.z ^ 2 = n at hsform
      change 2 * t.1.x ^ 2 + t.1.y ^ 2 + 32 * t.1.z ^ 2 = n at htform
      rw [hsx₂, hsy₂] at hsform
      rw [htx₂, hty₂] at htform
      omega
    · exact Or.inr ⟨hsx, htx⟩
end TunnellMap
