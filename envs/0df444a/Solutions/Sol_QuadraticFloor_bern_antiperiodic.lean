-- Prove2me | solution 1 for QuadraticFloor.bern_antiperiodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:05:44.05779+00:00
-- url     : https://prove2.me/submissions/8cdec65e-4008-432e-ba29-476e600b3764

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_bern_antiperiodic__37acfbc76d79


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (f : ℕ → ℂ) {h : ℕ} (hh : 0 < h) (hf : ∀ x, f (x + h) = -f x) :
    bern (2 * h) f = -(1 / 2) * ∑ x ∈ Icc 1 h, f x :=
  bern_antiperiodic' f hh hf
end QuadraticFloor
