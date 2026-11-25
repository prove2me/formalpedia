-- Prove2me | solution 1 for UpperTheory.Top.realBox
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:46:56.003657+00:00
-- url     : https://prove2.me/submissions/7751adf7-99cb-4174-9760-a97fe5200180

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_TwistForm
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_RealSplit
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_RealBox
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_isPrimOf_iff
import Theorems.Thm_UpperTheory_Top_realSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open Formalism.HC UpperTheory.Top
private theorem UpperTheory.Top.realBox_level {φ : Frame} (H : HostRaw φ) (χ : PChar)
    (h : H.IsCharE χ.χ) : χ.N ∣ H.QS * H.q * H.d := by
  obtain ⟨θ, hθ⟩ := h
  rw [H.isPrimOf_iff] at hθ
  subst hθ
  exact DirichletCharacter.conductor_dvd_level _
private theorem UpperTheory.Top.realBox_main (M : ℕ) (φ : Frame) (H : HostRaw φ) (eps Y X : ℝ)
    (hpr : ∀ l : ℕ, l.Prime → l ∣ H.QS → l ∣ 2 * M) (hM : ordCompl[2] H.QS ∣ M) (hg : PairGood M eps Y X H.q H.d)
    (χ : PChar) (hχ : H.IsCharE χ.χ) (hr : χ.IsReal) (hqd : H.q ∣ χ.N ∨ H.d ∣ χ.N) :
    ZeroBox (height M eps Y (if H.d ∣ χ.N then 1 else 0)) χ.χ ∧
      (χ.N : ℝ) ≤ height (ordCompl[2] H.QS) eps Y (if H.d ∣ χ.N then 1 else 0) := by
  have hP := hg.pair
  have hq := hP.q_prime
  have hd := hP.d_prime
  have hq8 := hP.q_mod
  have hd16 := hP.d_mod
  have hq2 : H.q ≠ 2 := by intro h; rw [h] at hq8; norm_num at hq8
  have hd2 : H.d ≠ 2 := by intro h; rw [h] at hd16; norm_num at hd16
  have hqd' : H.q ≠ H.d := by intro h; rw [h] at hq8; omega
  have hlev := UpperTheory.Top.realBox_level H χ hχ
  obtain ⟨ρ, i, j, hρr, hρN, hN, hval⟩ :=
    realSplit χ H.QS H.q H.d hr H.QS_pos hq hd hq2 hd2 hqd' H.QS_coprime hlev
  have hKdvd : ordCompl[2] H.QS ∣ H.QS := Nat.ordCompl_dvd _ _
  have hK0 : 0 < ordCompl[2] H.QS := Nat.ordCompl_pos 2 H.QS_pos.ne'
  have hnot : ∀ l, l.Prime → l ≠ 2 → l ∣ H.q * H.d → ¬ l ∣ ρ.N := by
    intro l hl hl2 hlqd hlρ
    have h8 := hlρ.trans hρN
    rcases (Nat.Prime.dvd_mul hl).1 h8 with h | h
    · have : l ∣ 2 := hl.dvd_of_dvd_pow (n := 3) (by norm_num; exact h)
      exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 this)
    · have h1 := Nat.dvd_gcd (h.trans hKdvd) hlqd
      rw [H.QS_coprime.gcd_eq_one] at h1
      exact hl.not_dvd_one h1
  have hqρ := hnot _ hq hq2 (dvd_mul_right _ _)
  have hdρ := hnot _ hd hd2 (dvd_mul_left _ _)
  have hcopN : ∀ a : ℕ, a.Coprime (2 * M * H.q * H.d) → a.Coprime χ.N := by
    intro a ha
    refine Nat.coprime_of_dvd fun l hl hla hlN => ?_
    have hl' : l ∣ 2 * M * H.q * H.d := by
      rcases (Nat.Prime.dvd_mul hl).1 (hlN.trans hlev) with h | h
      · rcases (Nat.Prime.dvd_mul hl).1 h with h | h
        · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (hpr l hl h) _) _
        · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _
      · exact Dvd.dvd.mul_left h _
    have h1 := Nat.dvd_gcd hla hl'
    rw [ha.gcd_eq_one] at h1
    exact hl.not_dvd_one h1
  have hind : An.Induces χ.χ (tw ρ.val H.q H.d i j) (2 * M * H.q * H.d) := by
    unfold An.Induces
    exact ⟨χ.prim, fun a ha => hval a (hcopN a ha)⟩
  have hi01 : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have hj01 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  have hij : i ≠ 0 ∨ j ≠ 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨rfl, rfl⟩ := hc
    rw [show H.q ^ ((0 : Fin 2) : ℕ) = 1 by simp, show H.d ^ ((0 : Fin 2) : ℕ) = 1 by simp,
      mul_one, mul_one] at hN
    rcases hqd with h | h <;> rw [hN] at h
    exacts [hqρ h, hdρ h]
  have hbox := hg.boxes ρ hρr (hρN.trans (mul_dvd_mul_left 8 hM)) i j hij χ.N χ.χ hind
  have hdq : ¬ H.d ∣ H.q := fun h => hqd' ((Nat.prime_dvd_prime_iff_eq hd hq).1 h).symm
  have hdqi : ∀ k : ℕ, ¬ H.d ∣ H.q ^ k := fun k h => hdq (hd.dvd_of_dvd_pow h)
  have hjd : (if H.d ∣ χ.N then (1 : Fin 2) else 0) = j := by
    rcases hj01 with rfl | rfl
    · rw [if_neg]
      rw [hN, show H.d ^ ((0 : Fin 2) : ℕ) = 1 by simp, mul_one]
      intro h
      rcases (Nat.Prime.dvd_mul hd).1 h with h | h
      exacts [hdρ h, hdqi _ h]
    · rw [if_pos]
      rw [hN]
      exact dvd_mul_of_dvd_right (dvd_pow_self _ (by simp)) _
  have hqe : (H.q : ℝ) ≤ Real.exp (Y ^ (eps / 5)) :=
    (Real.log_le_iff_le_exp (by exact_mod_cast hq.pos)).1 hP.q_up
  have hde : (H.d : ℝ) ≤ Real.exp (Y ^ (eps / 5) * Real.log Y ^ 2) :=
    (Real.log_le_iff_le_exp (by exact_mod_cast hd.pos)).1 hP.d_up
  have hρle : (ρ.N : ℝ) ≤ 8 * ((ordCompl[2] H.QS : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (by norm_num) hK0) hρN
  have hbound : (χ.N : ℝ) ≤ height (ordCompl[2] H.QS) eps Y j := by
    have hq1 : (1:ℝ) ≤ H.q := by exact_mod_cast hq.one_lt.le
    have hqi : (H.q:ℝ) ^ (i:ℕ) ≤ Real.exp (Y ^ (eps / 5)) :=
      (pow_le_pow_right₀ hq1 (Nat.lt_succ_iff.1 i.isLt)).trans (by rw [pow_one]; exact hqe)
    have hdj : (H.d:ℝ) ^ (j:ℕ) ≤ Real.exp (Y ^ (eps / 5) * Real.log Y ^ 2) ^ (j:ℕ) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hde _
    rw [hN, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
    unfold height
    exact mul_le_mul (mul_le_mul hρle hqi (by positivity) (by positivity)) hdj
      (by positivity) (by positivity)
  rw [hjd]
  exact ⟨hbox, hbound⟩
end

set_option autoImplicit false
open Formalism.HC UpperTheory.Top
namespace UpperTheory.Top
theorem _root_.solution :
    ∀ (M : ℕ) (φ : Frame) (H : HostRaw φ) (eps Y X : ℝ), 0 < M → (∀ l : ℕ, l.Prime → l ∣ H.QS → l ∣ 2 * M) → ordCompl[2] H.QS ∣ M →
      PairGood M eps Y X H.q H.d →
      (∀ χ : PChar, H.IsCharE χ.χ → χ.IsReal → (H.q ∣ χ.N ∨ H.d ∣ χ.N) →
        ZeroBox (height M eps Y (if H.d ∣ χ.N then 1 else 0)) χ.χ ∧
          (χ.N : ℝ) ≤ height (ordCompl[2] H.QS) eps Y (if H.d ∣ χ.N then 1 else 0)) ∧ RealBox H := by
  intro M φ H eps Y X _ hpr hM hg
  refine ⟨fun χ hχ hr hqd => UpperTheory.Top.realBox_main M φ H eps Y X hpr hM hg χ hχ hr hqd, ?_⟩
  intro ψ hψ hr hqd β hβ
  have h := (UpperTheory.Top.realBox_main M φ H eps Y X hpr hM hg ψ hψ hr hqd).1
  refine h (β : ℂ) (by simpa using hβ) ?_
  simp only [Complex.ofReal_im, abs_zero]
  unfold height
  positivity
end UpperTheory.Top
