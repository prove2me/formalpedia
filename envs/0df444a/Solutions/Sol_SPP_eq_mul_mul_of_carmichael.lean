-- Prove2me | solution 1 for SPP.eq_mul_mul_of_carmichael
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:15:36.909025+00:00
-- url     : https://prove2.me/submissions/762cfd9f-a3a8-4cd7-9017-e06991ffd361

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_FPP_Carmichael_card_primeFactors
import Theorems.Thm_FPP_Carmichael_not_isPrimePow
import Theorems.Thm_FPP_Carmichael_odd
import Theorems.Thm_FPP_Carmichael_squarefree
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
import Theorems.Thm_Subgroup_mem_closure_neg_one
import Theorems.Thm_ZMod_fst_chineseRemainder
import Theorems.Thm_ZMod_snd_chineseRemainder
import Theorems.Thm_ZMod_unitsMap_neg
import Theorems.Thm_exists_pow_prime_dvd_and_coprime_of_odd
attribute [local simp] P2M_ZMod_fst_chineseRemainder__e38dff19d888
attribute [local simp] P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
attribute [local simp] Subgroup.mem_closure_neg_one
attribute [local simp] ZMod.fst_chineseRemainder
attribute [local simp] ZMod.snd_chineseRemainder
attribute [local simp] ZMod.unitsMap_neg



set_option autoImplicit false
open Nat
open SPP
open Subgroup
variable {n : ℕ}
namespace SPP
theorem _root_.solution [hn : Fact (1 < n)] (hc : FPP.Carmichael n) (hnp : ¬n.Prime) :
    ∃ m₁ m₂ m₃, n = m₁ * m₂ * m₃ ∧ m₁.Coprime m₂ ∧ m₁.Coprime m₃ ∧ m₂.Coprime m₃ ∧
      2 < m₁ ∧ 2 < m₂ ∧ 2 < m₃ := by
    have h := hc.card_primeFactors hnp
    have hnpp := hc.not_isPrimePow hnp
    have hsf := hc.squarefree
    rcases (show 2 ≤ n from hn.out).eq_or_lt with rfl | hn2
    · simp [Nat.prime_two] at hnp
    have ho := hc.odd hn2
    obtain ⟨p, s, k, pp, spos, rfl, pcop, hk, hps⟩ :=
      exists_pow_prime_dvd_and_coprime_of_odd hn.out ho hnpp
    obtain rfl : s = 1 := by
      by_contra hs
      apply pow_two p ▸ squarefree_iff_prime_squarefree.mp hsf p pp
      use p ^ (s - 2) * k
      rw [← mul_assoc, ← pow_add,
        Nat.add_sub_cancel' (lt_of_le_of_ne spos.nat_succ_le (Ne.symm hs))]
    rw [p.pow_one] at *
    have hok : Odd k := ho.of_dvd_nat ⟨p, mul_comm _ _⟩
    obtain ⟨q, t, l, _, _, rfl, qcop, hl, hqt⟩ :=
      exists_pow_prime_dvd_and_coprime_of_odd hk.le hok <| by
        rintro ⟨q, t, pq, _, rfl⟩
        rw [primeFactors_mul (by positivity) (by positivity), pp.primeFactors,
          primeFactors_prime_pow (by positivity) pq.nat_prime, Finset.card_union,
          Finset.card_singleton, Finset.card_singleton] at h
        omega
    use p, q ^ t, l, (mul_assoc _ _ _).symm
    use pcop.coprime_mul_right_right, pcop.coprime_mul_left_right
end SPP
