-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_normalized_samples_16384
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T18:27:32.973551+00:00
-- url     : https://prove2.me/submissions/0b49784b-2713-43ca-90b0-f08bd0b62100

import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_guarded_samples
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block00
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block01
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block02
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block03
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block04
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block05
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block06
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block07
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block08
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block09
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block10
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block11
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block12
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block13
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block14
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_gamma_guard_block15
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHBatch01GammaPacketFacts
open RHBatch01GammaArithmetic RHBatch01GammaGuards
theorem all_guard (i : Nat) (hi : i < 16384) : guard (compute i) = true := by
  have hb : i / 1024 < 16 := by omega
  generalize hx : i / 1024 = b at hb
  interval_cases b
  · exact TaoFivePrimes.rh_batch01_height_gamma_guard_block00 i (by omega) (by omega)
  · exact TaoFivePrimes.rh_batch01_height_gamma_guard_block01 i (by omega) (by omega)
  · exact TaoFivePrimes.rh_batch01_height_gamma_guard_block02 i (by omega) (by omega)
  · exact TaoFivePrimes.rh_batch01_height_gamma_guard_block03 i (by omega) (by omega)
  · exact TaoFivePrimes.rh_batch01_height_gamma_guard_block04 i (by omega) (by omega)
  · exact TaoFivePrimes.rh_batch01_height_gamma_guard_block05 i (by omega) (by omega)
  · exact TaoFivePrimes.rh_batch01_height_gamma_guard_block06 i (by omega) (by omega)
  · exact TaoFivePrimes.rh_batch01_height_gamma_guard_block07 i (by omega) (by omega)
  · exact TaoFivePrimes.rh_batch01_height_gamma_guard_block08 i (by omega) (by omega)
  · exact TaoFivePrimes.rh_batch01_height_gamma_guard_block09 i (by omega) (by omega)
  · exact TaoFivePrimes.rh_batch01_height_gamma_guard_block10 i (by omega) (by omega)
  · exact TaoFivePrimes.rh_batch01_height_gamma_guard_block11 i (by omega) (by omega)
  · exact TaoFivePrimes.rh_batch01_height_gamma_guard_block12 i (by omega) (by omega)
  · exact TaoFivePrimes.rh_batch01_height_gamma_guard_block13 i (by omega) (by omega)
  · exact TaoFivePrimes.rh_batch01_height_gamma_guard_block14 i (by omega) (by omega)
  · exact TaoFivePrimes.rh_batch01_height_gamma_guard_block15 i (by omega) (by omega)
end RHBatch01GammaPacketFacts
#print axioms RHBatch01GammaPacketFacts.all_guard

theorem solution :
  ∀ i : Nat, i < 16384 →
  let n : Int := (i:Int)-8192
  let b : Nat := (3289999808*32+n).toNat
  let v := RHBatch01GammaArithmetic.compute i
  let D : Nat := RHBatch01LogData.D
  let z : ℂ := ((v.cos:ℂ)+(v.sin:ℂ)*Complex.I)/(D:ℂ)
  let phase : ℂ := if v.negative then starRingEnd ℂ z else z
  ∀ k : Nat, k < 26 →
    let m := RHBatch01MomentArithmetic.moment i v k
    ‖(Complex.Gamma (1/4+((b:ℂ)/64)*Complex.I)*
    Complex.exp (((Real.pi*((b:ℝ)/64)/2-((n:ℝ)/32)^2/800:ℝ):ℂ)))*((-2*(Real.pi:ℂ)*Complex.I*((n:ℂ)/32))^k/
      ((k.factorial:ℂ)*(512:ℂ)^k))-
      ((m.1:ℂ)+(m.2:ℂ)*Complex.I)/(2:ℂ)^80‖≤1/10^23 := by
  intro i hi
  exact (TaoFivePrimes.rh_batch01_height_guarded_samples i hi
    (RHBatch01GammaPacketFacts.all_guard i hi)).2
#print axioms solution
