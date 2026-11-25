-- Prove2me | solution 1 for P2M_Erdos1063_exists_exception__4b25d7e991f6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:28:29.060248+00:00
-- url     : https://prove2.me/submissions/c54d72c5-57fa-45b8-bf13-1c326c901048

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
public import Theorems.Thm_Erdos1063_valuation_bound

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {n k : ℕ} (hk : 2 ≤ k) (hkn : 2 * k ≤ n) :
    ¬ ∀ i < k, (n - i) ∣ n.choose k := by
  intro hall
  have hp : (k.minFac).Prime := Nat.minFac_prime (by omega)
  have hpk : k.minFac ∣ k := Nat.minFac_dvd k
  have h0 := valuation_bound (i0 := 0) hp hkn hpk hk (fun i hi _ => hall i hi)
  have h1 := valuation_bound (i0 := 1) hp hkn hpk hk (fun i hi _ => hall i hi)
  have := Fact.mk hp
  have ha : 1 ≤ padicValNat k.minFac k := one_le_padicValNat_of_dvd (by omega) hpk
  have d0 : k.minFac ∣ n - 0 := dvd_of_one_le_padicValNat (by omega)
  have d1 : k.minFac ∣ n - 1 := dvd_of_one_le_padicValNat (by omega)
  have hsub := Nat.dvd_sub d0 d1
  rw [show (n - 0) - (n - 1) = 1 by omega] at hsub
  exact hp.one_lt.ne' (Nat.dvd_one.mp hsub)
end Erdos1063
