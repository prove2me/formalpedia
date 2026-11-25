-- Prove2me | solution 1 for SmallRatio.coprime_rem_den
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:36:24.838448+00:00
-- url     : https://prove2.me/submissions/26853c7a-1a95-42dc-abfc-45c418b1f555

module
public import Definitions.Def_SmallRatio_AlongEuclid
public import Definitions.Def_SmallRatio_Legendre
public import Definitions.Def_SmallRatio_Main
public import Theorems.Thm_SmallRatio_coprime_p_h
public import Theorems.Thm_SmallRatio_pos_rem_of_le_steps
public import Theorems.Thm_SmallRatio_rem_den_identity
public import Theorems.Thm_SmallRatio_rem_le_h


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p)
include hp hh hhp
namespace SmallRatio
theorem _root_.solution {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ steps p h) :
    Nat.Coprime (rem p h j) (den p h j) := by
  have hc := coprime_p_h hp hh hhp
  have e := rem_den_identity hh hhp hc hj
  set d := Nat.gcd (rem p h j) (den p h j)
  have hdp : d ∣ p := by
    rw [← e]
    exact dvd_add (dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _)
  rcases (Nat.dvd_prime hp).1 hdp with h1 | h1
  · exact h1
  · exfalso
    have hr := pos_rem_of_le_steps hh hhp hc hj
    have hrh := rem_le_h hh hhp hc hj1 hj
    have hd : d ∣ rem p h j := Nat.gcd_dvd_left _ _
    rw [h1] at hd
    have := Nat.le_of_dvd hr hd
    omega
end SmallRatio
