-- Prove2me | solution 1 for P2M_FixedOrderFactor_sum_orbitAvg_eq_zero__21e3915dbad5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:07:09.239685+00:00
-- url     : https://prove2.me/submissions/6cfd6203-cc05-4d54-bb36-53b6ce4f075c

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
public import Theorems.Thm_P2M_FixedOrderFactor_sum_orbitAvg_mul__4157f1f1226d

set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {s : ℕ} (hs : 1 < s) : ∑ t ∈ range s, orbitAvg s t = 0 := by
  have h := sum_orbitAvg_mul' (s := s) (by omega) 1
  simp only [one_mul] at h
  rw [h, ite_eq_right_iff.2]
  intro hd
  have := Nat.le_of_dvd one_pos hd
  omega
end FixedOrderFactor
