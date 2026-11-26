-- Prove2me | solution 1 for QuadraticFloor.floorSum_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:06:41.942731+00:00
-- url     : https://prove2.me/submissions/986f8408-1629-4fe8-8928-010d8e5c9752

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_floorSum_three__e43f4ec98ff4


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (floorSum 3 1 0 p : ℂ) = 1 - (1 / 2) *
      (bern (24 * p) (fun x => (eta p x : ℂ) * (if 3 ∣ x then 0 else 1)) +
        bern (24 * p) (fun x => (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) *
          (legendreSym 3 x : ℂ))) :=
  floorSum_three' hp2 hp3
end QuadraticFloor
