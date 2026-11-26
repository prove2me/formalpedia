-- Prove2me | solution 1 for PascalMinusOne.exceptional_mixed_no_one_borrow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:24:19.709229+00:00
-- url     : https://prove2.me/submissions/8f7d09ca-cc3c-4f36-89b9-f4ec247bc1c9

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_PascalMinusOne_not_dvd_add_same_parity_powers
import Theorems.Thm_PascalMinusOne_mixed_eq_sum_two_powers
import Theorems.Thm_PascalMinusOne_evenDigitSum_zero
import Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
import Theorems.Thm_PascalMinusOne_mod_pow_succ_eq_mod_add_digitAt
import Theorems.Thm_PascalMinusOne_not_carryAt_iff_mod_pow_le
import Theorems.Thm_PascalMinusOne_oddDigitSum_zero
import Theorems.Thm_PascalMinusOne_padicVal_choose_eq_carryCount
import Theorems.Thm_PascalMinusOne_parityDigitSums_cons
import Theorems.Thm_PascalMinusOne_parityDigitSums_nil
import Theorems.Thm_PascalMinusOne_signedZeroSum_m_zero
import Theorems.Thm_PascalMinusOne_signedZeroSum_one_one
import Theorems.Thm_PascalMinusOne_signedZeroSum_zero_m
attribute [local simp] PascalMinusOne.evenDigitSum_zero
attribute [local simp] PascalMinusOne.mem_admissibleIndices_iff
attribute [local simp] PascalMinusOne.oddDigitSum_zero
attribute [local simp] PascalMinusOne.parityDigitSums_cons
attribute [local simp] PascalMinusOne.parityDigitSums_nil
attribute [local simp] PascalMinusOne.signedZeroSum_m_zero
attribute [local simp] PascalMinusOne.signedZeroSum_one_one
attribute [local simp] PascalMinusOne.signedZeroSum_zero_m



set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p = m - 1)
    (hmN : m ∣ N) (hNm : m < N)
    (hmixed : evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) :
    ∀ k, Admissible N m k → padicValNat p (N.choose k) ≠ 1 := by
  classical
  intro k hk hval
  letI : Fact p.Prime := ⟨hp⟩
  rcases hk with ⟨hkpos, hklt, hmk⟩
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 < p := hp.one_lt
  have hp2 : 2 ≤ p := hp.two_le
  have hpmMod : p % m = m - 1 := by
    rw [hpm]
    exact Nat.mod_eq_of_lt (by omega)
  have hpSucc : p + 1 = m := by omega
  obtain ⟨s, t, hst, hNpow, hopposite⟩ :=
    mixed_eq_sum_two_powers hm hp hpmMod hmN hmixed
  have hpowst : p ^ s < p ^ t :=
    Nat.pow_lt_pow_right hp1 hst
  have hpowle : p ^ t ≤ N := by
    rw [hNpow]
    omega
  have hNlt2 : N < 2 * p ^ t := by
    rw [hNpow]
    omega
  have hNltTop : N < p ^ (t + 1) := by
    calc
      N < 2 * p ^ t := hNlt2
      _ ≤ p * p ^ t := Nat.mul_le_mul_right (p ^ t) hp2
      _ = p ^ (t + 1) := by rw [pow_succ, Nat.mul_comm]
  have hlog : Nat.log p N = t :=
    Nat.log_eq_of_pow_le_of_lt_pow hpowle hNltTop
  have hkn : k ≤ N := hklt.le
  have hcount : carryCount p N k (t + 1) = 1 := by
    rw [← padicVal_choose_eq_carryCount
      (p := p) (n := N) (k := k) hkn (by rw [hlog]; omega)]
    exact hval
  rw [carryCount] at hcount
  obtain ⟨i, hfilter⟩ := Finset.card_eq_one.mp hcount
  have himem :
      i ∈ (Finset.Ico 1 (t + 1)).filter (fun j ↦ CarryAt p N k j) := by
    rw [hfilter]
    simp
  have hirange : i ∈ Finset.Ico 1 (t + 1) :=
    (Finset.mem_filter.mp himem).1
  have hiCarry : CarryAt p N k i :=
    (Finset.mem_filter.mp himem).2
  have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hirange).1
  have hit : i ≤ t := by
    have := (Finset.mem_Ico.mp hirange).2
    omega
  have hnocarry {j : ℕ} (hjt : j ≤ t) (hji : j ≠ i) :
      ¬ CarryAt p N k j := by
    by_cases hj0 : j = 0
    · subst j
      apply
        (not_carryAt_iff_mod_pow_le
          (p := p) (n := N) (k := k) (i := 0) hp0 hkn).2
      change k % 1 ≤ N % 1
      rw [Nat.mod_one, Nat.mod_one]
    · intro hjcarry
      have hjmem :
          j ∈ (Finset.Ico 1 (t + 1)).filter (fun r ↦ CarryAt p N k r) := by
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr hj0, by omega⟩
        · exact hjcarry
      rw [hfilter] at hjmem
      have hjeq : j = i := by simpa using hjmem
      exact hji hjeq
  have hprefix_of_nocarry {j : ℕ} (hj : ¬ CarryAt p N k j) :
      k % p ^ j ≤ N % p ^ j :=
    (not_carryAt_iff_mod_pow_le
      (p := p) (n := N) (k := k) (i := j) hp0 hkn).1 hj
  have hprefix_gt_of_carry {j : ℕ} (hj : CarryAt p N k j) :
      N % p ^ j < k % p ^ j := by
    have hnotle : ¬ k % p ^ j ≤ N % p ^ j := by
      intro hle
      exact
        ((not_carryAt_iff_mod_pow_le
          (p := p) (n := N) (k := k) (i := j) hp0 hkn).2 hle) hj
    omega
  have hNmod_low {j : ℕ} (hjs : j ≤ s) :
      N % p ^ j = 0 := by
    rw [hNpow, Nat.add_mod,
      Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow p hjs),
      Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow p (hjs.trans hst.le))]
    simp
  have hNmod_mid {j : ℕ} (hsj : s < j) (hjt : j ≤ t) :
      N % p ^ j = p ^ s := by
    rw [hNpow, Nat.add_mod,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right hp1 hsj),
      Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow p hjt)]
    simpa using Nat.mod_eq_of_lt (Nat.pow_lt_pow_right hp1 hsj)
  have hkmod_mono (j : ℕ) :
      k % p ^ j ≤ k % p ^ (j + 1) := by
    rw [mod_pow_succ_eq_mod_add_digitAt]
    omega
  have hiloc : i = s ∨ i = t := by
    by_cases his : i = s
    · exact Or.inl his
    by_cases hit' : i = t
    · exact Or.inr hit'
    rcases lt_or_gt_of_ne his with hislt | hsilt
    · have hinext : ¬ CarryAt p N k (i + 1) :=
        hnocarry (by omega) (by omega)
      have hnext := hprefix_of_nocarry hinext
      have hcur := hprefix_gt_of_carry hiCarry
      have hNi : N % p ^ i = 0 :=
        hNmod_low (by omega)
      have hNnext : N % p ^ (i + 1) = 0 :=
        hNmod_low (by omega)
      have hkmono := hkmod_mono i
      rw [hNi] at hcur
      rw [hNnext] at hnext
      omega
    · have hilt : i < t := by omega
      have hinext : ¬ CarryAt p N k (i + 1) :=
        hnocarry (by omega) (by omega)
      have hnext := hprefix_of_nocarry hinext
      have hcur := hprefix_gt_of_carry hiCarry
      have hNi : N % p ^ i = p ^ s :=
        hNmod_mid hsilt hit
      have hNnext : N % p ^ (i + 1) = p ^ s :=
        hNmod_mid (by omega) (by omega)
      have hkmono := hkmod_mono i
      rw [hNi] at hcur
      rw [hNnext] at hnext
      omega
  rcases hiloc with his | hitop
  · subst i
    have hs1 : 1 ≤ s := hi1
    have hcur := hprefix_gt_of_carry hiCarry
    have hNs : N % p ^ s = 0 := hNmod_low le_rfl
    rw [hNs] at hcur
    have hkmods_pos : 0 < k % p ^ s := hcur
    have hprevnc : ¬ CarryAt p N k (s - 1) :=
      hnocarry (by omega) (by omega)
    have hprev := hprefix_of_nocarry hprevnc
    have hNprev : N % p ^ (s - 1) = 0 :=
      hNmod_low (by omega)
    rw [hNprev] at hprev
    have hkmodprev_zero : k % p ^ (s - 1) = 0 :=
      Nat.eq_zero_of_le_zero hprev
    let a := digitAt p k (s - 1)
    have hksform : k % p ^ s = p ^ (s - 1) * a := by
      have hrec := mod_pow_succ_eq_mod_add_digitAt p k (s - 1)
      have hsadd : s - 1 + 1 = s := Nat.sub_add_cancel hs1
      rw [hsadd, hkmodprev_zero] at hrec
      simpa [a] using hrec
    have ha0 : 0 < a := by
      by_contra hna
      have haeq : a = 0 := Nat.eq_zero_of_not_pos hna
      rw [haeq, mul_zero] at hksform
      omega
    have halt : a < p := by
      dsimp [a, digitAt]
      exact Nat.mod_lt _ hp0
    have htNc : ¬ CarryAt p N k t :=
      hnocarry le_rfl (by omega)
    have htPrefix := hprefix_of_nocarry htNc
    have hNt : N % p ^ t = p ^ s :=
      hNmod_mid hst le_rfl
    rw [hNt] at htPrefix
    have hkmodt_le : k % p ^ t ≤ p ^ s := htPrefix
    have hkmodt_lt : k % p ^ t < p ^ s := by
      by_contra hnot
      have heq : k % p ^ t = p ^ s := by omega
      have hnested :=
        Nat.mod_mod_of_dvd k (Nat.pow_dvd_pow p hst.le)
      rw [heq] at hnested
      simp at hnested
      omega
    have hkmodt_eq : k % p ^ t = k % p ^ s := by
      have hnested :=
        Nat.mod_mod_of_dvd k (Nat.pow_dvd_pow p hst.le)
      rw [Nat.mod_eq_of_lt hkmodt_lt] at hnested
      exact hnested
    let b := k / p ^ t
    have hb_lt : b < 2 := by
      dsimp [b]
      rw [Nat.div_lt_iff_lt_mul (pow_pos hp0 t)]
      exact hklt.trans hNlt2
    have hb1 : b ≤ 1 := by omega
    have hkform : k = a * p ^ (s - 1) + b * p ^ t := by
      calc
        k = k % p ^ t + p ^ t * (k / p ^ t) :=
          (Nat.mod_add_div k (p ^ t)).symm
        _ = a * p ^ (s - 1) + b * p ^ t := by
          rw [hkmodt_eq, hksform]
          simp [b, Nat.mul_comm]
    have hsflip : Even (s - 1) ↔ ¬ Even s := by
      rw [Nat.even_sub' hs1, Nat.not_even_iff_odd]
      simp
    have hop : ¬ Even s ↔ Even t := by
      constructor
      · intro hsnot
        by_contra htnot
        apply hopposite
        exact
          ⟨fun hsE ↦ (hsnot hsE).elim,
            fun htE ↦ (htnot htE).elim⟩
      · intro htE hsE
        apply hopposite
        exact ⟨fun _ ↦ htE, fun _ ↦ hsE⟩
    have hpar : Even (s - 1) ↔ Even t :=
      hsflip.trans hop
    have habpos : 0 < a + b :=
      Nat.add_pos_left ha0 b
    have hablt : a + b < m := by
      rw [← hpSucc]
      omega
    have hbad :=
      not_dvd_add_same_parity_powers
        (m := m) (p := p) (a := a) (b := b)
        (u := s - 1) (v := t)
        hm hpmMod habpos hablt hpar
    apply hbad
    rw [← hkform]
    exact hmk
  · subst i
    have ht1 : 1 ≤ t := hi1
    have hsNc : ¬ CarryAt p N k s :=
      hnocarry hst.le (by omega)
    have hsPrefix := hprefix_of_nocarry hsNc
    have hNs : N % p ^ s = 0 := hNmod_low le_rfl
    rw [hNs] at hsPrefix
    have hkmods_zero : k % p ^ s = 0 :=
      Nat.eq_zero_of_le_zero hsPrefix
    have hprevNc : ¬ CarryAt p N k (t - 1) :=
      hnocarry (by omega) (by omega)
    have hprevPrefix := hprefix_of_nocarry hprevNc
    have hNprev_le : N % p ^ (t - 1) ≤ p ^ s := by
      by_cases hle : t - 1 ≤ s
      · rw [hNmod_low hle]
        omega
      · have hsltprev : s < t - 1 := Nat.lt_of_not_ge hle
        rw [hNmod_mid hsltprev (by omega)]
    have hkmodprev_le : k % p ^ (t - 1) ≤ p ^ s :=
      hprevPrefix.trans hNprev_le
    have hsleprev : s ≤ t - 1 := by omega
    have hkdvdps : p ^ s ∣ k :=
      Nat.dvd_of_mod_eq_zero hkmods_zero
    have hprevdvd : p ^ s ∣ k % p ^ (t - 1) :=
      (Nat.dvd_mod_iff (Nat.pow_dvd_pow p hsleprev)).2 hkdvdps
    let b := (k % p ^ (t - 1)) / p ^ s
    have hprevform : k % p ^ (t - 1) = b * p ^ s := by
      dsimp [b]
      exact (Nat.div_mul_cancel hprevdvd).symm
    have hbmul : b * p ^ s ≤ 1 * p ^ s := by
      rw [← hprevform]
      simpa using hkmodprev_le
    have hb1 : b ≤ 1 :=
      Nat.le_of_mul_le_mul_right hbmul (pow_pos hp0 s)
    have hcur := hprefix_gt_of_carry hiCarry
    have hNt : N % p ^ t = p ^ s :=
      hNmod_mid hst le_rfl
    rw [hNt] at hcur
    have hkmodt_gt : p ^ s < k % p ^ t := hcur
    let a := digitAt p k (t - 1)
    have halt : a < p := by
      dsimp [a, digitAt]
      exact Nat.mod_lt _ hp0
    have hktform :
        k % p ^ t =
          k % p ^ (t - 1) + p ^ (t - 1) * a := by
      have hrec := mod_pow_succ_eq_mod_add_digitAt p k (t - 1)
      have htadd : t - 1 + 1 = t := Nat.sub_add_cancel ht1
      rw [htadd] at hrec
      simpa [a] using hrec
    have ha0 : 0 < a := by
      by_contra hna
      have haeq : a = 0 := Nat.eq_zero_of_not_pos hna
      rw [haeq, mul_zero, add_zero] at hktform
      omega
    let q := k / p ^ t
    have hq_lt : q < 2 := by
      dsimp [q]
      rw [Nat.div_lt_iff_lt_mul (pow_pos hp0 t)]
      exact hklt.trans hNlt2
    have hq1 : q ≤ 1 := by omega
    have hkdecomp :
        k = k % p ^ t + p ^ t * q := by
      simpa [q] using (Nat.mod_add_div k (p ^ t)).symm
    have hq0 : q = 0 := by
      by_contra hqne
      have hqpos : 0 < q := Nat.pos_of_ne_zero hqne
      have hqeq : q = 1 := by omega
      rw [hqeq, mul_one] at hkdecomp
      rw [hNpow] at hklt
      omega
    have hkform :
        k = b * p ^ s + a * p ^ (t - 1) := by
      calc
        k = k % p ^ t := by rw [hkdecomp, hq0]; simp
        _ = k % p ^ (t - 1) + p ^ (t - 1) * a := hktform
        _ = b * p ^ s + a * p ^ (t - 1) := by
          rw [hprevform]
          ac_rfl
    have htflip : Even (t - 1) ↔ ¬ Even t := by
      rw [Nat.even_sub' ht1, Nat.not_even_iff_odd]
      simp
    have hop : Even s ↔ ¬ Even t := by
      constructor
      · intro hsE htE
        apply hopposite
        exact ⟨fun _ ↦ htE, fun _ ↦ hsE⟩
      · intro htnot
        by_contra hsnot
        apply hopposite
        exact
          ⟨fun hsE ↦ (hsnot hsE).elim,
            fun htE ↦ (htnot htE).elim⟩
    have hpar : Even s ↔ Even (t - 1) :=
      hop.trans htflip.symm
    have hbapos : 0 < b + a :=
      Nat.add_pos_right b ha0
    have hbalt : b + a < m := by
      rw [← hpSucc]
      omega
    have hbad :=
      not_dvd_add_same_parity_powers
        (m := m) (p := p) (a := b) (b := a)
        (u := s) (v := t - 1)
        hm hpmMod hbapos hbalt hpar
    apply hbad
    rw [← hkform]
    exact hmk
end PascalMinusOne
