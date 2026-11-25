-- Prove2me | solution 1 for UpperTheory.HF.cond_rd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:57:08.110667+00:00
-- url     : https://prove2.me/submissions/5a7733e0-3861-4ddd-b7b4-84c56d45e96a

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogRdSum
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdLe
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdFormula
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LayerBot
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CondESpec
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CardImgOneDvd
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CondRd
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGroup
import Theorems.Thm_Formalism_HC_Frame_hostGroup
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_mem_imgOne
import Theorems.Thm_UpperTheory_HF_card_imgOne_dvd
import Theorems.Thm_UpperTheory_HF_condE_spec
import Theorems.Thm_UpperTheory_HF_layer_bot
import Theorems.Thm_UpperTheory_HF_log_rd_sum
import Theorems.Thm_UpperTheory_HF_vd_formula
import Theorems.Thm_UpperTheory_HF_vd_le
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
private theorem half_le_vd {φ : Frame} (H : HostAx φ) {l : ℕ} (hl : l.Prime) :
    (H.condE.factorization l : ℝ) ≤ 2 * H.vdH l := by
  have heN := (layer_bot H.toHostRaw hl (Nat.zero_le (H.condN.factorization l))).2.2
  rw [vd_formula H hl]
  have hnn : ∀ c : ℕ, (0 : ℝ) ≤ 1 - 1 / (c : ℝ) := by
    intro c
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp
    · have h1 : (1 : ℝ) / c ≤ 1 := by
        rw [div_le_one (by exact_mod_cast hc)]
        exact_mod_cast hc
      linarith
  have hhalf : ∀ c : ℕ, c ≠ 1 → (1 : ℝ) / 2 ≤ 1 - 1 / (c : ℝ) := by
    intro c hc
    rcases c with _ | _ | c
    · norm_num
    · exact absurd rfl hc
    · have h1 : (1 : ℝ) / ((c + 1 + 1 : ℕ) : ℝ) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by push_cast; linarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)])
      linarith
  calc (H.condE.factorization l : ℝ)
      = 2 * ∑ j ∈ Finset.range (H.condE.factorization l), (1 / 2 : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ 2 * ∑ j ∈ Finset.range (H.condE.factorization l),
        (1 - 1 / (Nat.card (UpperTheory.HF.Formalism.HC.HostRaw.imgOne H.toHostRaw
          (H.condN / l ^ H.condN.factorization l * l ^ j)) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro j hj
        apply hhalf
        rw [Ne, Subgroup.card_eq_one]
        have hjN : j ≤ H.condN.factorization l := (Finset.mem_range.1 hj).le.trans heN
        rw [(layer_bot H.toHostRaw hl hjN).1]
        exact not_le.2 (Finset.mem_range.1 hj)
    _ ≤ 2 * ∑ j ∈ Finset.range (H.condN.factorization l),
        (1 - 1 / (Nat.card (UpperTheory.HF.Formalism.HC.HostRaw.imgOne H.toHostRaw
          (H.condN / l ^ H.condN.factorization l * l ^ j)) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 heN)
          (fun j _ _ => hnn _)
end

set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ), H.rd ≤ H.condE ∧ Real.log H.rd ≤ Real.log H.condE ∧ Real.log H.condE ≤ Real.log H.condN ∧ (H.condE : ℝ) ≤ H.rd ^ 2 ∧ 4 * φ.ord ≤ H.condE.totient ∧ 4 * φ.ord ∣ H.condE.totient ∧ 4 * φ.ord ≤ H.condE := by
  intro φ H
  obtain ⟨hEN, hE0, hspec⟩ := condE_spec H.toHostRaw
  have hN0 := H.condN_ne_zero
  obtain ⟨-, hlogrd, -, hrd0⟩ := log_rd_sum H
  have hE0' : (0 : ℝ) < H.condE := by exact_mod_cast hE0
  have logE : Real.log H.condE =
      ∑ l ∈ H.condN.primeFactors, (H.condE.factorization l : ℝ) * Real.log l := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    apply Finset.sum_subset (Nat.primeFactors_mono hEN hN0)
    intro l _ hl
    have h0 : H.condE.factorization l = 0 := by
      rwa [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hl
    simp [h0]
  have hb : Real.log H.rd ≤ Real.log H.condE := by
    rw [hlogrd, logE]
    apply Finset.sum_le_sum
    intro l hl
    have hlp := Nat.prime_of_mem_primeFactors hl
    exact mul_le_mul_of_nonneg_right (vd_le H hlp).2
      (Real.log_nonneg (by exact_mod_cast hlp.one_lt.le))
  have hd : Real.log H.condE ≤ 2 * Real.log H.rd := by
    rw [hlogrd, logE, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    have hlp := Nat.prime_of_mem_primeFactors hl
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (half_le_vd H hlp)
      (Real.log_nonneg (by exact_mod_cast hlp.one_lt.le))
  have ha : H.rd ≤ H.condE := (Real.log_le_log_iff hrd0 hE0').1 hb
  have hcE : (H.condE : ℝ) ≤ H.rd ^ 2 := by
    rw [← Real.log_le_log_iff hE0' (by positivity), Real.log_pow]
    push_cast
    linarith
  have hc : Real.log H.condE ≤ Real.log H.condN :=
    Real.log_le_log hE0' (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hEN)
  have htop : UpperTheory.HF.Formalism.HC.HostRaw.imgOne H.toHostRaw 1 = ⊤ := by
    ext g
    simp only [Subgroup.mem_top, iff_true]
    obtain ⟨u, rfl⟩ := H.der.art_surj g
    exact (UpperTheory.HF.Formalism.HC.HostRaw.mem_imgOne H.toHostRaw (one_dvd _) _).2 ⟨u, Nat.modEq_one, rfl⟩
  have hbot : UpperTheory.HF.Formalism.HC.HostRaw.imgOne H.toHostRaw H.condE = ⊥ := (hspec _ hEN).2 dvd_rfl
  have hdvd := card_imgOne_dvd H.toHostRaw (one_dvd H.condE) hEN
  rw [htop, hbot, Subgroup.card_top, Subgroup.card_bot, Nat.totient_one, Nat.div_one, one_mul,
    (φ.hostGroup).1] at hdvd
  have htpos : 0 < H.condE.totient := Nat.totient_pos.2 hE0
  exact ⟨ha, hb, hc, hcE, Nat.le_of_dvd htpos hdvd, hdvd,
    (Nat.le_of_dvd htpos hdvd).trans (Nat.totient_le _)⟩
end UpperTheory.HF
