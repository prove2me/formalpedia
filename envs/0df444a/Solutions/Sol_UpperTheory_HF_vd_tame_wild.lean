-- Prove2me | solution 1 for UpperTheory.HF.vd_tame_wild
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:37:30.66944+00:00
-- url     : https://prove2.me/submissions/3082a146-09a0-4ef4-a65f-edfa3ab26325

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdFormula
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LayerBot
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CardImgOneDvd
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdTameWild
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_imgOne_anti
import Theorems.Thm_UpperTheory_HF_layer_bot
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
private theorem half_le {c : ℕ} (h : 2 ≤ c) : (1 : ℝ) / 2 ≤ 1 - 1 / (c : ℝ) := by
  have h2 : (2 : ℝ) ≤ c := by exact_mod_cast h
  have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2
  linarith
private theorem term_nonneg {c : ℕ} (h : 0 < c) : (0 : ℝ) ≤ 1 - 1 / (c : ℝ) := by
  have hc : (1 : ℝ) ≤ c := by exact_mod_cast h
  have h1 : 1 / (c : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hc
  linarith
end

set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → (¬ l ∣ H.el l → H.vdH l = 1 - 1 / (H.el l : ℝ)) ∧ (l ∣ H.el l → 1 ≤ H.vdH l) ∧ (¬ l ∣ H.el l → H.sl l = 1) := by
  intro φ H l hl
  set v := H.condN.factorization l with hv
  set e := (HostRaw.condE H.toHostRaw).factorization l with he
  let G : ℕ → Subgroup φ.GG := fun j => HostRaw.imgOne H.toHostRaw (H.condN / l ^ v * l ^ j)
  have hev : e ≤ v := (layer_bot H.toHostRaw (j := 0) hl (Nat.zero_le _)).2.2
  have hbot : ∀ j, j ≤ v → (G j = ⊥ ↔ e ≤ j) := fun j hj => (layer_bot H.toHostRaw hl hj).1
  have hdvd : ∀ j, j ≤ e → Nat.card (G j) ∣ (l ^ e).totient / (l ^ j).totient :=
    fun j hj => (layer_bot H.toHostRaw hl (hj.trans hev)).2.1 hj
  have hcard_one : ∀ j, j ≤ v → (Nat.card (G j) = 1 ↔ e ≤ j) :=
    fun j hj => Subgroup.card_eq_one.trans (hbot j hj)
  have hpos : ∀ j, j ≤ v → 0 < Nat.card (G j) := by
    intro j hjv
    by_cases hje : j ≤ e
    · have h1 : (l ^ j).totient ∣ (l ^ e).totient := Nat.totient_dvd_of_dvd (pow_dvd_pow l hje)
      have h2 : 0 < (l ^ j).totient := Nat.totient_pos.2 (pow_pos hl.pos _)
      have h3 : 0 < (l ^ e).totient := Nat.totient_pos.2 (pow_pos hl.pos _)
      exact Nat.pos_of_dvd_of_pos (hdvd j hje) (Nat.div_pos (Nat.le_of_dvd h3 h1) h2)
    · push_neg at hje
      rw [(hcard_one j hjv).2 hje.le]
      exact Nat.one_pos
  have hge : ∀ j, j < e → 2 ≤ Nat.card (G j) := by
    intro j hj
    have hjv : j ≤ v := by omega
    have h1 := hpos j hjv
    have h2 : Nat.card (G j) ≠ 1 := fun h => by
      have := (hcard_one j hjv).1 h
      omega
    omega
  have hanti : 1 ≤ v → Nat.card (G 1) ∣ Nat.card (G 0) := by
    intro h1v
    apply Subgroup.card_dvd_of_le
    apply HostRaw.imgOne_anti _ (mul_dvd_mul_left _ (pow_dvd_pow l (by norm_num)))
    calc H.condN / l ^ v * l ^ 1 ∣ H.condN / l ^ v * l ^ v := mul_dvd_mul_left _ (pow_dvd_pow l h1v)
      _ = H.condN := Nat.div_mul_cancel (Nat.ordProj_dvd _ _)
  have hel : H.el l = Nat.card (G 0) := by
    show Nat.card (HostRaw.imgOne H.toHostRaw (H.condN / l ^ v)) =
      Nat.card (HostRaw.imgOne H.toHostRaw (H.condN / l ^ v * l ^ 0))
    rw [pow_zero, mul_one]
  have hsum : H.vdH l = ∑ j ∈ Finset.range v, (1 - 1 / (Nat.card (G j) : ℝ)) := vd_formula H hl
  have hsl : H.sl l = max 1 e := rfl
  have key1 : ¬ l ∣ H.el l → e ≤ 1 := by
    intro hnd
    by_contra hlt
    push_neg at hlt
    have h1v : 1 ≤ v := by omega
    have hd := hdvd 1 hlt.le
    rw [Nat.totient_prime_pow hl (by omega), pow_one, Nat.totient_prime hl,
      Nat.mul_div_cancel _ (Nat.sub_pos_of_lt hl.one_lt)] at hd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hl).1 hd
    have hne : Nat.card (G 1) ≠ 1 := fun h => by
      have := (hcard_one 1 h1v).1 h
      omega
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hk')
    have hl1 : l ∣ Nat.card (G 1) := hk' ▸ dvd_pow_self l hk0
    exact hnd (hel ▸ hl1.trans (hanti h1v))
  have key2 : l ∣ H.el l → 2 ≤ e := by
    intro hd
    rw [hel] at hd
    by_contra hlt
    have hcases : e = 0 ∨ e = 1 := by omega
    rcases hcases with h0 | h1
    · rw [(hcard_one 0 (Nat.zero_le _)).2 (by omega)] at hd
      exact hl.not_dvd_one hd
    · have hd0 := hdvd 0 (by omega)
      rw [h1] at hd0
      simp [Nat.totient_prime hl] at hd0
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt hl.one_lt) (hd.trans hd0)
      have := hl.two_le
      omega
  refine ⟨fun hnd => ?_, fun hd => ?_, fun hnd => ?_⟩
  · have he1 := key1 hnd
    rw [hsum, hel]
    refine Finset.sum_eq_single 0 ?_ ?_
    · intro j hj hj0
      have hjv : j ≤ v := (Finset.mem_range.1 hj).le
      rw [(hcard_one j hjv).2 (by omega)]
      norm_num
    · intro h0
      have hv0 : v = 0 := by simpa using h0
      rw [(hcard_one 0 (Nat.zero_le _)).2 (by omega)]
      norm_num
  · rw [hsum]
    have h2e := key2 hd
    have h2v : 2 ≤ v := h2e.trans hev
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range v := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_range]
      omega
    have h01 : (0 : ℕ) ≠ 1 := by norm_num
    calc (1 : ℝ) = 1 / 2 + 1 / 2 := by norm_num
      _ ≤ (1 - 1 / (Nat.card (G 0) : ℝ)) + (1 - 1 / (Nat.card (G 1) : ℝ)) :=
          add_le_add (half_le (hge 0 (by omega))) (half_le (hge 1 (by omega)))
      _ = ∑ j ∈ ({0, 1} : Finset ℕ), (1 - 1 / (Nat.card (G j) : ℝ)) :=
          (Finset.sum_pair (f := fun j => (1 - 1 / (Nat.card (G j) : ℝ))) h01).symm
      _ ≤ ∑ j ∈ Finset.range v, (1 - 1 / (Nat.card (G j) : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j hj _ => term_nonneg (hpos j (Finset.mem_range.1 hj).le))
  · rw [hsl]
    exact max_eq_left (key1 hnd)
end UpperTheory.HF
