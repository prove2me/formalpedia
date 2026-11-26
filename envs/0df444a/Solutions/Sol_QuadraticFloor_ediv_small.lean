-- Prove2me | solution 1 for QuadraticFloor.ediv_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:51.855921+00:00
-- url     : https://prove2.me/submissions/846a3807-b9ac-4eff-90e4-c157d9c3cf2f

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution {v : ℤ} {P : ℤ} (hP : |v| < P) :
    v / P = if v < 0 then -1 else 0 := by
  have hP0 : 0 < P := lt_of_le_of_lt (abs_nonneg v) hP
  rw [abs_lt] at hP
  split_ifs with h
  · have hv := Int.emod_add_mul_ediv v P
    have hr0 := Int.emod_nonneg v hP0.ne'
    have hrl := Int.emod_lt_of_pos v hP0
    set q := v / P
    set r := v % P
    have h1 : q < 0 := by
      by_contra hq; rw [not_lt] at hq; nlinarith
    have h2 : -2 < q := by
      by_contra hq; rw [not_lt] at hq; nlinarith
    omega
  · exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
end QuadraticFloor
