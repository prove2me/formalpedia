-- Prove2me | solution 1 for SmallRatio.coprime_p_h
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:20:54.007085+00:00
-- url     : https://prove2.me/submissions/54f62acd-54e0-45ad-ad35-b8abfbe38c13

module
public import Definitions.Def_SmallRatio_AlongEuclid
public import Definitions.Def_SmallRatio_Legendre
public import Definitions.Def_SmallRatio_Main

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p)
include hp hh hhp
namespace SmallRatio
theorem _root_.solution : Nat.Coprime p h := Nat.coprime_of_lt_prime hh.ne' hhp hp
end SmallRatio
