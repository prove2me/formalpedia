-- Prove2me | solution 1 for P2M_MohP3_Wt_yOrd_mul__b3d090251f18
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:21:54.762232+00:00
-- url     : https://prove2.me/submissions/0c65c36b-825e-4081-96d2-49202a15aab5

module
public import Mathlib
public import Definitions.Def_MohP3_Order
public import Theorems.Thm_MohP3_Wt_yOrd_mono
public import Theorems.Thm_MohP3_Wt_yOrd_mul

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution {p q : PowerSeries k} {m n r : ℕ} (hr : r ≤ m + n)
    (hp : YOrd p m) (hq : YOrd q n) : YOrd (p * q) r :=
  yOrd_mono hr (yOrd_mul hp hq)
end MohP3.Wt
