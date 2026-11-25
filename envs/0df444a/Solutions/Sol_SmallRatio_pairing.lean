-- Prove2me | solution 1 for SmallRatio.pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:38:13.730219+00:00
-- url     : https://prove2.me/submissions/beb021f5-f511-4651-9510-deb85e2647cf

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
public import Theorems.Thm_SmallRatio_legendre_pairing


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
    (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (huv : Nat.Coprime u v) (hsmall : 2 * u * v < k)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hcong : (k : ℤ) ∣ (h : ℤ) * v - ε * u) :
    ∃ j ∈ Icc 1 (steps k h), rem k h j = u ∧ den k h j = v ∧ ε = (-1) ^ (j + 1) :=
  legendre_pairing hh hhk hc u v hu hv huv hsmall ε hε hcong
end SmallRatio
