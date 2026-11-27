-- Prove2me | solution 1 for P2M_MohP3_Wt_wOrd_mul__c4d0f86c750f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:22:01.106568+00:00
-- url     : https://prove2.me/submissions/06a3fd7f-8805-4f0b-9b4a-e27f411d3aac

module
public import Mathlib
public import Definitions.Def_MohP3_Order
public import Theorems.Thm_MohP3_Wt_wOrd_mono
public import Theorems.Thm_MohP3_Wt_wOrd_mul

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution {F G : MvPowerSeries (Fin 3) k} {m n p : ℕ} (hp : p ≤ m + n)
    (hF : WOrd F m) (hG : WOrd G n) : WOrd (F * G) p :=
  wOrd_mono hp (wOrd_mul hF hG)
end MohP3.Wt
