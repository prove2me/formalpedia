-- Prove2me | solution 1 for UpperTheory.HF.vd_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:49.623889+00:00
-- url     : https://prove2.me/submissions/edc0522b-bc36-4650-aa29-cb105e6fdb39

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdFormula
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RhoArt
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdTwo
import Theorems.Thm_Formalism_HC_Der_Rd_hH_art
import Theorems.Thm_Formalism_HC_Der_Rd_hcl_eq_one
import Theorems.Thm_Formalism_HC_Der_Rd_rho_nonneg
import Theorems.Thm_Formalism_HC_Der_Rd_rho_two
import Theorems.Thm_Formalism_HC_Der_Rd_sum_totient_pow
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_UpperTheory_HF_rho_art
import Theorems.Thm_UpperTheory_HF_vd_formula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
private theorem rho_sum {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {e : ℕ} (h2 : 2 ^ (e + 2) ∣ N)
    (hU : ∀ u ∈ U, ZMod.unitsMap h2 u = 1 ∨ ZMod.unitsMap h2 u = -1) :
    (e : ℝ) + 1 - 1 / 2 ^ e ≤
      ∑ j ∈ Finset.range (N.factorization 2), Formalism.HC.Der.Rd.rho U (ordCompl[2] N * 2 ^ j) := by
  have hN : N ≠ 0 := NeZero.ne N
  have ha : e + 2 ≤ N.factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN).1 h2
  have hM : Nat.Coprime 2 (ordCompl[2] N) := Nat.coprime_ordCompl Nat.prime_two hN
  have hdvd : 2 ^ (e + 2) * ordCompl[2] N ∣ N := by
    have h := mul_dvd_mul_right (pow_dvd_pow 2 ha) (ordCompl[2] N)
    rwa [Nat.ordProj_mul_ordCompl_eq_self] at h
  have ht : ∑ j ∈ Finset.range (e + 2), (((2 ^ j).totient : ℕ) : ℝ) = 2 ^ (e + 1) := by
    have h := Formalism.HC.Der.Rd.sum_totient_pow Nat.prime_two (e + 1)
    rw [show e + 1 + 1 = e + 2 by ring] at h
    exact_mod_cast h
  have hc : ∀ n : ℕ, ∑ j ∈ Finset.range (n + 2), (if j < 2 then (1:ℝ) else 0) = 2 := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    | succ k ih =>
      rw [show k + 1 + 2 = (k + 2) + 1 by ring, Finset.sum_range_succ, ih]
      simp
  calc (e : ℝ) + 1 - 1 / 2 ^ e
      = ∑ j ∈ Finset.range (e + 2),
          (1 - ((((2 ^ j).totient : ℕ) : ℝ) + if j < 2 then 1 else 0) / 2 ^ (e + 1)) := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib, ht, hc e]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        push_cast
        field_simp
        ring
    _ ≤ ∑ j ∈ Finset.range (e + 2), Formalism.HC.Der.Rd.rho U (ordCompl[2] N * 2 ^ j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j ≤ e + 2 := (Finset.mem_range.1 hj).le
        rw [mul_comm]
        exact Formalism.HC.Der.Rd.rho_two U hM hdvd hj' hU
    _ ≤ ∑ j ∈ Finset.range (N.factorization 2), Formalism.HC.Der.Rd.rho U (ordCompl[2] N * 2 ^ j) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ha)
          (fun _ _ _ => Formalism.HC.Der.Rd.rho_nonneg _ _)
end

set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ), (φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ)) ≤ H.vdH 2 ∧ 11 / 4 ≤ H.vdH 2 ∧ 4 + 2 * H.vdH 2 ≤ 2 + 3 * H.vdH 2 := by
  intro φ H
  haveI : NeZero H.condN := ⟨by
    have h := H.QS_pos
    have hq := (HostRaw.q_prime H.toHostRaw).pos
    have hd := (HostRaw.d_prime H.toHostRaw).pos
    show H.QS * H.q * H.d ≠ 0
    positivity⟩
  have hU : ∀ u ∈ H.art.ker, ZMod.unitsMap (Formalism.HC.Der.Rd.two_dvd H.toHostRaw) u = 1 ∨
      ZMod.unitsMap (Formalism.HC.Der.Rd.two_dvd H.toHostRaw) u = -1 := by
    intro u hu
    apply Formalism.HC.Der.Rd.hcl_eq_one
    rw [← Formalism.HC.Der.Rd.hH_art, MonoidHom.mem_ker.1 hu]
    exact map_one _
  have hs := rho_sum H.art.ker (Formalism.HC.Der.Rd.two_dvd H.toHostRaw) hU
  have hv : H.vdH 2 = ∑ j ∈ Finset.range (H.condN.factorization 2),
      Formalism.HC.Der.Rd.rho H.art.ker (ordCompl[2] H.condN * 2 ^ j) := by
    rw [vd_formula H Nat.prime_two]
    apply Finset.sum_congr rfl
    intro j hj
    rw [rho_art H.toHostRaw]
    apply Nat.dvd_trans (Nat.mul_dvd_mul_left _ (pow_dvd_pow 2 (Finset.mem_range.1 hj).le))
    rw [mul_comm, Nat.ordProj_mul_ordCompl_eq_self]
  have he : 2 ≤ φ.e := H.two_le_e
  have hrp : (2 : ℝ) ^ (-(φ.e : ℝ)) = 1 / 2 ^ φ.e := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]
  have h4 : (4 : ℝ) ≤ 2 ^ φ.e := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ φ.e := pow_le_pow_right₀ (by norm_num) he
  have hinv : 1 / (2 : ℝ) ^ φ.e ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) h4
  have hecast : (2 : ℝ) ≤ φ.e := by exact_mod_cast he
  have hmain : (φ.e : ℝ) + 1 - 1 / 2 ^ φ.e ≤ H.vdH 2 := by rw [hv]; exact hs
  rw [hrp]
  refine ⟨hmain, ?_, ?_⟩ <;> linarith
end UpperTheory.HF
