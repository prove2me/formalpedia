-- Prove2me | solution 1 for PascalExtremes.extremalRows_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:00:46.595888+00:00
-- url     : https://prove2.me/submissions/3d86a7a8-85ac-4936-a240-60fceeb6d2b0

module
public import Definitions.Def_PascalExtremes_TargetA
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Theorems.Thm_PascalExtremes_targetA_attainment

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p m : ℕ} (hp : p.Prime) (hm2 : 2 ≤ m) (hpm : ¬ p ∣ m) :
    (extremalRows p m).Nonempty := by
  obtain ⟨N, hrow, hval⟩ := targetA_attainment hp hm2 hpm
  exact ⟨N, hrow, hval⟩
end PascalExtremes
