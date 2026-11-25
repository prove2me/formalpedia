-- Prove2me | solution 1 for SmallRatio.pairs_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:38:14.207355+00:00
-- url     : https://prove2.me/submissions/2905f836-b163-4121-ad2e-76c617489f2f

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
public import Theorems.Thm_SmallRatio_coprime_rem_den


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p) :
    ∀ j, 1 ≤ j → j ≤ steps p h → Nat.Coprime (rem p h j) (den p h j) :=
  fun _ hj1 hj => coprime_rem_den hp hh hhp hj1 hj
end SmallRatio
