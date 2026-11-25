-- Prove2me | solution 1 for OptimalAffinity.oa2x2_ratesPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:53:28.59315+00:00
-- url     : https://prove2.me/submissions/4ab7880a-a092-42e9-9f08-d52eb54bc7ce

module
public import Mathlib
public import Definitions.Def_proofs_OptimalAffinity_Source

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution :
    ∀ r : Reaction, 0 < oa2x2.kPlus r ∧ 0 < oa2x2.kMinus r := by
  intro r
  fin_cases r <;> norm_num [oa2x2]
end OptimalAffinity
