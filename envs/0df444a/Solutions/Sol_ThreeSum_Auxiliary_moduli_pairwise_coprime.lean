-- Prove2me | solution 1 for ThreeSum.Auxiliary.moduli_pairwise_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:38:57.939742+00:00
-- url     : https://prove2.me/submissions/afb188ec-0d73-4009-ab0d-16606eea861d

import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Mathlib.RingTheory.Coprime.Lemmas
import Definitions.Def_Submission_ThreeSum_Auxiliary

set_option autoImplicit false
open ThreeSum ThreeSum.Auxiliary
open Finset
open scoped BigOperators
namespace ThreeSum.Auxiliary
theorem _root_.solution (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) :
    (moduli C : Set ℤ).Pairwise (fun a b => IsCoprime a b) := by
  intro a ha b hb hne
  obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hb
  have hpq : p ≠ q := by intro h; subst q; exact hne rfl
  have hc : p.Coprime q := (Nat.coprime_primes (hC p hp) (hC q hq)).mpr hpq
  exact hc.isCoprime
end ThreeSum.Auxiliary
