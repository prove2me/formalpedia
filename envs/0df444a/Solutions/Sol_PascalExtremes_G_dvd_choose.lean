-- Prove2me | solution 1 for PascalExtremes.G_dvd_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:54:23.485475+00:00
-- url     : https://prove2.me/submissions/4e5790bc-be46-4268-81b2-729b7064da8b

module
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Basic

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution {N m k : ℕ} (hk : k ∈ admissibleIndices N m) :
    G N m ∣ N.choose k := by
  exact Finset.gcd_dvd hk
end PascalExtremes
