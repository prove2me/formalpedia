-- Prove2me | solution 1 for SZ.digitReal_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:09.827293+00:00
-- url     : https://prove2.me/submissions/2dbaefec-f272-45ea-965e-600baa743b5f

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_digitReal_lt_of_zero_two

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {d d' : ℕ → ℤ} (h : IsDigits 3 d) (h' : IsDigits 3 d')
    (hd : ∀ j, d j = 0 ∨ d j = 2) (hd' : ∀ j, d' j = 0 ∨ d' j = 2)
    {i : ℕ} (hagree : ∀ j, j < i → d j = d' j) (hne : d i ≠ d' i) :
    digitReal 3 d ≠ digitReal 3 d' := by
  rcases hd i with h0 | h0 <;> rcases hd' i with h0' | h0'
  · exact absurd (h0.trans h0'.symm) hne
  · exact ne_of_lt (digitReal_lt_of_zero_two h h' hagree h0 h0')
  · exact ne_of_gt (digitReal_lt_of_zero_two h' h (fun j hj => (hagree j hj).symm) h0' h0)
  · exact absurd (h0.trans h0'.symm) hne
end SZ
