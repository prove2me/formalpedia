-- Prove2me | solution 1 for PascalMinusOne.G_dvd_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:18:38.833119+00:00
-- url     : https://prove2.me/submissions/a89cd440-4209-425b-ae35-0616c1d30870

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Basic

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution {N m k : ℕ} (hk : k ∈ admissibleIndices N m) :
    G N m ∣ N.choose k := by
  exact Finset.gcd_dvd hk
end PascalMinusOne
