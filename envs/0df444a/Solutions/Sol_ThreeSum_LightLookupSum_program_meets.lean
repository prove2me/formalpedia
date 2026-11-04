-- Prove2me | solution 1 for ThreeSum.LightLookupSum.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:31:16.707198+00:00
-- url     : https://prove2.me/submissions/c6a08fb3-3b89-4c08-8ae8-037db7d22d21

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightLookupSum
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2

set_option autoImplicit false
open ThreeSum ThreeSum.LightLookupSum
open Light Finset
open scoped BigOperators
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLookupSum
theorem _root_.solution
    {μ : ℕ → ℤ} {keys table n p B : ℕ} (key f : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hkeys : keys+n ≤ lim.space) (htable : table+p ≤ lim.space)
    (hkey : ∀ i < n, μ (keys+i) = (key i : ℤ))
    (hrange : ∀ i < n, key i < p)
    (hread : ∀ r < p, μ (table+r) = (f r : ℤ))
    (hvalue : ∀ r < p, f r ≤ B)
    (hword : (n*B : ℕ) ≤ lim.word) :
    Meets lim program 0 d [keys, table, n, p] μ (time n)
      (fun r μ' => r = (prefixSum f key n : ℤ) ∧ μ' = μ) :=
  meets rfl key f hw hkeys htable hkey hrange hread hvalue hword
end ThreeSum.LightLookupSum
