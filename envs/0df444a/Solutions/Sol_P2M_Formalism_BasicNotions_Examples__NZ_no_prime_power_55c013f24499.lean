-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_no_prime_power_55c013f24499
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:32:40.616325+00:00
-- url     : https://prove2.me/submissions/c9ca56bd-cb5a-447b-ad60-6cee9390229b

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_coprime_n_8914bd4d6568
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
variable {d : ℕ} (hd : 1 ≤ d) (u : (Fbar g)ˣ) (hu : orderOf u = g ^ d - 1)
include hd hu
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {q0 ℓ : ℕ} (hℓ : ℓ.Prime) (hq0 : q0.Prime) (hq2 : q0 ≠ 2) (h2g : 2 ∣ g - 1)
    (hqg : q0 ∣ g - 1) (i c : ℕ) : ((u : Fbar g) ^ (g ^ i)) ^ (ℓ ^ c) ≠ 1 := by
  intro h
  have h1 : u ^ (g ^ i * ℓ ^ c) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, pow_mul, h]; rfl)
  have h2 : g ^ d - 1 ∣ ℓ ^ c :=
    ((coprime_n d hd).pow_right i).dvd_of_dvd_mul_left (hu ▸ orderOf_dvd_of_pow_eq_one h1)
  have h3 : g - 1 ∣ g ^ d - 1 := by simpa using Nat.sub_dvd_pow_sub_pow g 1 d
  have e1 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).mp
    (Nat.prime_two.dvd_of_dvd_pow ((h2g.trans h3).trans h2))
  have e2 := (Nat.prime_dvd_prime_iff_eq hq0 hℓ).mp (hq0.dvd_of_dvd_pow ((hqg.trans h3).trans h2))
  exact hq2 (e2.trans e1.symm)
end Formalism.BasicNotions.Examples₂.NZ
