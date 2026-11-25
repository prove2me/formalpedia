-- Prove2me | solution 1 for OptimalAffinity.oa2x2_inverseWitness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:54:30.770259+00:00
-- url     : https://prove2.me/submissions/e3f96f21-b691-443d-8491-98fba6192fff

module
public import Mathlib
public import Definitions.Def_proofs_OptimalAffinity_Source

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution :
    (-1 : ℤ) * 1 + 2 * 1 = 1 ∧
    (-1 : ℤ) * 2 + 2 * 1 = 0 ∧
    (1 : ℤ) * 1 + (-1) * 1 = 0 ∧
    (1 : ℤ) * 2 + (-1) * 1 = 1 := by
  norm_num
end OptimalAffinity
