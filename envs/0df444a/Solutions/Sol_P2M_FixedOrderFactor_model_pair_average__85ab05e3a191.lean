-- Prove2me | solution 1 for P2M_FixedOrderFactor_model_pair_average__85ab05e3a191
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:37.726419+00:00
-- url     : https://prove2.me/submissions/a279ed68-b6bb-49af-b982-3a4b97c3e62c

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
public import Definitions.Def_FixedOrderFactor_ModelPairs
public import Theorems.Thm_FixedOrderFactor_sum_omega_zpow
public import Theorems.Thm_FixedOrderFactor_pow_iff_dvd_valuations
public import Theorems.Thm_FixedOrderFactor_zPow_mul_conj

set_option autoImplicit true
@[expose] public section
public section
open Finset Complex
open FixedOrderFactor
open Classical
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : 0 < r) (S : Finset Nat.Primes) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hS : ∀ q : Nat.Primes, (q : ℕ) ∣ m * n → q ∈ S) :
    (1 / (r : ℂ) ^ S.card) * ∑ j : S → Fin r, zPow r S j m * starRingEnd ℂ (zPow r S j n) =
      if ∃ x : ℚ, (m : ℚ) / n = x ^ r then 1 else 0 := by
  simp_rw [zPow_mul_conj]
  rw [← Fintype.prod_sum (fun (q : S) (k : Fin r) => ω r ^ (((k : ℕ) : ℤ) *
      ((m.factorization (q : Nat.Primes) : ℤ) - n.factorization (q : Nat.Primes))))]
  simp_rw [sum_omega_zpow hr]
  rw [pow_iff_dvd_valuations hr hm hn hS]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  split_ifs with h
  · rw [Finset.prod_congr rfl (fun q _ => if_pos (h q.1 q.2)), Finset.prod_const,
      Finset.card_univ, Fintype.card_coe]
    field_simp
  · push Not at h
    obtain ⟨q, hqS, hq⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ ⟨q, hqS⟩) (if_neg hq), mul_zero]
end FixedOrderFactor
