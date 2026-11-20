-- Prove2me | solution 1 for QuantumSixJ.sum_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @igor.kh
-- created : 2026-11-13T10:30:18.909919+00:00
-- url     : https://prove2.me/submissions/58b0bc8d-5f84-4373-acc3-1a51119d7032

import Theorems.Thm_QuantumSixJ_scalar_foundations
import Theorems.Thm_QuantumSixJ_tet_two_evaluations
import Definitions.Def_QuantumSixJRecurrences
import Theorems.Thm_QuantumSixJ_sum_prefactor_match

noncomputable section
open QuantumSixJ
open scoped BigOperators QuantumSixJ Classical

private def q_ne_zero := QuantumSixJ.scalar_foundations.1
private def q_denominator_ne_zero := QuantumSixJ.scalar_foundations.2.1
private def qInt_ne_zero := QuantumSixJ.scalar_foundations.2.2.1
private def qFactorial_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.1
private def delta_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.1
private def theta_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.1
private def h_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.1
private def x_ne_zero := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.1
private def tet_summand_support_bounds := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.2.1
private def tet_appendix_bounds_within_coarse := QuantumSixJ.scalar_foundations.2.2.2.2.2.2.2.2.2.1

open QuantumSixJ
open scoped QuantumSixJ

private theorem qFactorial_inv_shift (n : ℤ) : (⟬n - 1⟭!)⁻¹ = ⟬n⟭ * (⟬n⟭!)⁻¹ := by
  by_cases hn : n ≤ 0
  · rcases lt_or_eq_of_le hn with hneg | hzero
    · have hprev : n - 1 < 0 := by omega
      simp [qFactorial, hneg, hprev]
    · subst n
      norm_num [qFactorial, qInt]
  · have hn0 : 0 ≤ n := by omega
    have hp0 : 0 ≤ n - 1 := by omega
    have hset : Finset.Icc (1 : ℤ) n = insert n (Finset.Icc 1 (n - 1)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnmem : n ∉ Finset.Icc (1 : ℤ) (n - 1) := by
      intro hmem
      have := (Finset.mem_Icc.mp hmem).2
      omega
    have hstep : ⟬n⟭! = ⟬n⟭ * ⟬n - 1⟭! := by
      simp only [qFactorial, if_neg (not_lt.mpr hn0), if_neg (not_lt.mpr hp0)]
      rw [hset, Finset.prod_insert hnmem]
    rw [← div_eq_mul_inv, eq_div_iff (qFactorial_ne_zero n hn0), hstep]
    field_simp [qFactorial_ne_zero (n - 1) hp0]

private theorem tet_special_evaluations :
    (∀ a b l : ℤ, 0 < a → 0 < b → Admissible a b l →
      ⟬a⟭ * ⟬b⟭ * tetSum a a b b l 2 = θ a b l * Λ a b l) ∧
    (∀ a d j : ℤ, 0 < a → Admissible a d j → Admissible a d (j + 2) →
      ⟬a⟭ * tetSum a a (j + 2) j d 2 =
        ⟬(a + d - j) / 2⟭ * θ (j + 2) a d) := by
  constructor
  · exact QuantumSixJ.tet_two_evaluations.2.2.1
  · intro a d j ha hj hj2
    have h1 : Admissible a (j + 2) d := by dsimp [Admissible] at *; omega
    have h2 : Admissible a j d := by dsimp [Admissible] at *; omega
    simpa only [min_eq_right (show j ≤ j + 2 by omega),
      max_eq_left (show j ≤ j + 2 by omega)] using
      QuantumSixJ.tet_two_evaluations.2.2.2.1 a (j + 2) j d ha h1 h2 (Or.inl rfl)

namespace PartTetCertificateAlgebra
open QuantumSixJ
open scoped QuantumSixJ

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem result (A B C E F j S : ℤ) :
    let D := E + F - C - j
    let G := A + B - j
    let nm := ⟬A - j + 1⟭ * ⟬B - j + 1⟭ * ⟬A + 1⟭ * ⟬B + 1⟭
    let np := ⟬E - C + 1⟭ * ⟬F - D + 1⟭ * ⟬F - C + 1⟭ * ⟬E - D + 1⟭
    let la := ⟬A - j⟭ * ⟬E - C⟭ - ⟬F - D⟭ * ⟬A + 2⟭
    let lb := ⟬B - j⟭ * ⟬F - C⟭ - ⟬E - D⟭ * ⟬B + 2⟭
    let ll := ⟬F - B⟭ * ⟬E - A⟭ - ⟬G - D⟭ * ⟬C + 2⟭
    let nb := -(la * lb + ll * ⟬j⟭ * ⟬j + 2⟭)
    let dm := ⟬S - A + 1⟭ * ⟬S - B + 1⟭
    let dp := ⟬E - S + 1⟭ * ⟬F - S + 1⟭
    let p := fun t : ℤ =>
      ⟬2⟭ * (⟬j + 2⟭ * ⟬t - E - 1⟭ *
        (⟬j⟭ * ⟬F - A + 1⟭ * ⟬t - B⟭ +
          ⟬B - j + 1⟭ * ⟬A + 1⟭ * ⟬F - t + 1⟭) -
        ⟬j⟭ * ⟬F - C + 1⟭ * ⟬F - D + 1⟭ * ⟬t - A⟭ * ⟬t - B⟭)
    nm * ⟬2⟭ * ⟬j + 2⟭ * ⟬E - S⟭ * ⟬F - S⟭ * dp +
    nb * ⟬j + 1⟭ * dm * dp +
    np * ⟬2⟭ * ⟬j⟭ * ⟬S - A⟭ * ⟬S - B⟭ * dm +
    ⟬S + 2⟭ * ⟬G - S⟭ * dp * p (S + 1) +
    ⟬S - C⟭ * ⟬S - D⟭ * dm * p S = 0 := by
  dsimp only
  unfold qInt
  simp only [zpow_add₀ q_ne_zero, zpow_sub₀ q_ne_zero, zpow_neg,
    zpow_natCast]
  field_simp [q_ne_zero, q_denominator_ne_zero, zpow_ne_zero]
  <;> ring

end PartTetCertificateAlgebra
private def tet_certificate_algebra := PartTetCertificateAlgebra.result

namespace PartTetCommonWeight
open QuantumSixJ
open QuantumSixJ.Certificate
open scoped QuantumSixJ

set_option maxHeartbeats 2000000

private lemma invstep (n : ℤ) : (⟬n⟭!)⁻¹ = ⟬n + 1⟭ * (⟬n + 1⟭!)⁻¹ := by
  simpa using qFactorial_inv_shift (n + 1)

private lemma invstep2 (n : ℤ) :
    (⟬n⟭!)⁻¹ = ⟬n + 1⟭ * ⟬n + 2⟭ * (⟬n + 2⟭!)⁻¹ := by
  rw [invstep n, invstep (n + 1)]
  simp only [show n + 1 + 1 = n + 2 by omega]
  ring

private lemma fstep (n : ℤ) (hn : 0 ≤ n) : ⟬n + 1⟭! = ⟬n + 1⟭ * ⟬n⟭! := by
  have hset : Finset.Icc (1 : ℤ) (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc (1 : ℤ) n := by
    intro hk
    have := (Finset.mem_Icc.mp hk).2
    omega
  simp only [qFactorial, if_neg (show ¬n + 1 < 0 by omega), if_neg (not_lt.mpr hn)]
  rw [hset, Finset.prod_insert hnot]

theorem result (A B C E F j S : ℤ) (hS : 0 ≤ S) :
    let D := E + F - C - j
    let G := A + B - j
    let W := commonWeight A B C E F j S
    let dm := ⟬S - A + 1⟭ * ⟬S - B + 1⟭
    let dp := ⟬E - S + 1⟭ * ⟬F - S + 1⟭
    (rawSummand (A - 1) (B - 1) C D (E - 1) (F - 1) G S =
      W * ⟬E - S⟭ * ⟬F - S⟭ * dp) ∧
    (rawSummand A B C D E F G S = W * dm * dp) ∧
    (rawSummand (A + 1) (B + 1) C D (E + 1) (F + 1) G S =
      W * ⟬S - A⟭ * ⟬S - B⟭ * dm) ∧
    (flux A B C E F j S =
      W * ⟬S - C⟭ * ⟬S - D⟭ * dm * scaledMultiplier A B C E F j S) ∧
    (flux A B C E F j (S + 1) =
      -W * ⟬S + 2⟭ * ⟬G - S⟭ * dp * scaledMultiplier A B C E F j (S + 1)) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [rawSummand, commonWeight, div_eq_mul_inv, mul_inv_rev]
    conv_lhs => rw [invstep2 (E - 1 - S), invstep2 (F - 1 - S)]
    simp only [show S - (A - 1) = S - A + 1 by omega,
      show S - (B - 1) = S - B + 1 by omega,
      show E - 1 - S + 1 = E - S by omega,
      show F - 1 - S + 1 = F - S by omega,
      show E - 1 - S + 2 = E - S + 1 by omega,
      show F - 1 - S + 2 = F - S + 1 by omega]
    ring
  · simp only [rawSummand, commonWeight, div_eq_mul_inv, mul_inv_rev]
    conv_lhs => rw [invstep (S - A), invstep (S - B), invstep (E - S), invstep (F - S)]
    ring
  · simp only [rawSummand, commonWeight, div_eq_mul_inv, mul_inv_rev]
    conv_lhs => rw [invstep2 (S - (A + 1)), invstep2 (S - (B + 1))]
    simp only [show S - (A + 1) + 1 = S - A by omega,
      show S - (B + 1) + 1 = S - B by omega,
      show S - (A + 1) + 2 = S - A + 1 by omega,
      show S - (B + 1) + 2 = S - B + 1 by omega,
      show E + 1 - S = E - S + 1 by omega,
      show F + 1 - S = F - S + 1 by omega]
    ring
  · simp only [flux, rawSummand, commonWeight, div_eq_mul_inv, mul_inv_rev]
    conv_lhs => rw [invstep (S - A), invstep (S - B), invstep (S - (C + 1)),
      invstep (S - (E + F - C - j + 1))]
    simp only [show S - (C + 1) + 1 = S - C by omega,
      show S - (E + F - C - j + 1) + 1 = S - (E + F - C - j) by omega,
      show E + 1 - S = E - S + 1 by omega,
      show F + 1 - S = F - S + 1 by omega]
    ring
  · have hs : (-1 : Scalar) ^ (S + 1) = -((-1 : Scalar) ^ S) := by
      rw [zpow_add₀ (by norm_num : (-1 : Scalar) ≠ 0)]
      simp
    have hf : ⟬S + 1 + 1⟭! = ⟬S + 2⟭ * ⟬S + 1⟭! := by
      simpa [add_assoc] using fstep (S + 1) (by omega)
    simp only [flux, rawSummand, commonWeight, div_eq_mul_inv, mul_inv_rev, hs, hf]
    conv_lhs => rw [invstep (A + B - j - (S + 1)),
      invstep (E + 1 - (S + 1)), invstep (F + 1 - (S + 1))]
    simp only [show S + 1 - A = S - A + 1 by omega,
      show S + 1 - B = S - B + 1 by omega,
      show S + 1 - (C + 1) = S - C by omega,
      show S + 1 - (E + F - C - j + 1) = S - (E + F - C - j) by omega,
      show A + B - j - (S + 1) + 1 = A + B - j - S by omega,
      show E + 1 - (S + 1) + 1 = E - S + 1 by omega,
      show F + 1 - (S + 1) + 1 = F - S + 1 by omega]
    ring

end PartTetCommonWeight
private def tet_common_weight := PartTetCommonWeight.result

namespace PartTetFluxEndpoints
open QuantumSixJ
open QuantumSixJ.Certificate
open scoped QuantumSixJ

theorem result (a b c d j l : ℤ)
    (hj : hAdmissible a b c d j) (hl : vAdmissible a b c d l) (hpos : 0 < j) :
    let A := tetA a b c d j l
    let B := tetB a b c d j l
    flux (A 0) (A 1) (A 2) (B 0) (B 1) j 0 = 0 ∧
    flux (A 0) (A 1) (A 2) (B 0) (B 1) j (sumLength a b c d j l : ℤ) = 0 := by
  have hc : 0 - (tetA a b c d j l 2 + 1) < 0 := by
    simp only [vAdmissible, Admissible] at hl
    simp [tetA]
    omega
  have hg : tetA a b c d j l 0 + tetA a b c d j l 1 - j -
      (sumLength a b c d j l : ℤ) < 0 := by
    simp only [hAdmissible, vAdmissible, Admissible] at hj hl
    simp [tetA, sumLength]
    omega
  constructor
  · simp only [flux, rawSummand]
    have hz : ⟬0 - (tetA a b c d j l 2 + 1)⟭! = 0 := by
      exact if_pos hc
    rw [hz]
    simp
  · simp only [flux, rawSummand]
    have hz : ⟬tetA a b c d j l 0 + tetA a b c d j l 1 - j -
        (sumLength a b c d j l : ℤ)⟭! = 0 := by
      exact if_pos hg
    rw [hz]
    simp

end PartTetFluxEndpoints
private def tet_flux_endpoints := PartTetFluxEndpoints.result

private def tet_prefactor_match := QuantumSixJ.sum_prefactor_match

namespace PartTetExceptional
open QuantumSixJ
open QuantumSixJ.Certificate
open scoped QuantumSixJ BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace TetExceptionalProof

private lemma zero_edge (a b l : ℤ) (hab : Admissible a b l) :
    tetSum a b b a 0 l = θ a b l := by
  let s := (a + b + l) / 2
  have har := hab
  rcases har with ⟨ha, hb, hl, h1, h2, h3, hp⟩
  have hs : 0 ≤ s := by dsimp [s]; omega
  have hsa : 0 ≤ s - a := by dsimp [s]; omega
  have hsb : 0 ≤ s - b := by dsimp [s]; omega
  have hsl : 0 ≤ a + b - s := by dsimp [s]; omega
  have hidx : s - l = a + b - s := by dsimp [s]; omega
  have hj : hAdmissible a b b a 0 := by
    constructor <;> dsimp [Admissible] <;> omega
  have hv : vAdmissible a b b a l := by
    refine ⟨hab, ?_⟩
    dsimp [Admissible]
    omega
  have hA : tetA a b b a 0 l = ![a, b, s, s] := by
    ext i
    fin_cases i <;> simp [tetA] <;> (try dsimp [s]) <;> omega
  have hB : tetB a b b a 0 l = ![s, s, a + b] := by
    ext i
    fin_cases i <;> simp [tetB] <;> (try dsimp [s]) <;> omega
  have support (S : ℤ) (hne : tetSummand a b b a 0 l S ≠ 0) : S = s := by
    have hr := (tet_summand_support_bounds a b b a 0 l S hj hv).mp hne
    simp only [hA, hB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons, Matrix.head_fin_const, max_le_iff, le_min_iff] at hr
    omega
  have hsum : (∑ S ∈ Finset.Icc 0 (a + b + b + a + 0 + l),
      tetSummand a b b a 0 l S) = tetSummand a b b a 0 l s := by
    apply Finset.sum_eq_single s
    · intro S _ hne
      by_contra ht
      exact hne (support S ht)
    · intro hnot
      exfalso
      apply hnot
      simp only [Finset.mem_Icc]
      constructor <;> dsimp [s] <;> omega
  rw [tetSum, if_pos ⟨hj, hv⟩, hsum, θ, if_pos hab]
  simp [tetSummand, hA, hB, Fin.prod_univ_succ,
    show ⟬(0 : ℤ)⟭! = 1 by norm_num [qFactorial]]
  change _ = (-1 : Scalar) ^ s * ⟬s + 1⟭! * ⟬s - a⟭! * ⟬s - b⟭! * ⟬s - l⟭! /
    (⟬a⟭! * ⟬b⟭! * ⟬l⟭!)
  rw [hidx]
  field_simp [qFactorial_ne_zero a ha, qFactorial_ne_zero b hb,
    qFactorial_ne_zero l hl, qFactorial_ne_zero (s - a) hsa,
    qFactorial_ne_zero (s - b) hsb, qFactorial_ne_zero (a + b - s) hsl]
  <;> ring

private lemma permute (a b l : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hab : Admissible a b l) : tetSum a b b a 2 l = tetSum a a b b l 2 := by
  have hj : hAdmissible a b b a 2 := by
    constructor <;> dsimp [Admissible] <;> omega
  have hv : vAdmissible a b b a l := by
    refine ⟨hab, ?_⟩
    dsimp [Admissible] at hab ⊢
    omega
  have hj' : hAdmissible a a b b l := ⟨hab, hab⟩
  have hv' : vAdmissible a a b b 2 := by
    constructor <;> dsimp [Admissible] <;> omega
  rw [tetSum, if_pos ⟨hj, hv⟩, tetSum, if_pos ⟨hj', hv'⟩]
  have hA1 : (a + a + 2) / 2 = a + 1 := by omega
  have hA2 : (b + b + 2) / 2 = b + 1 := by omega
  have hB1 : (b + a + 2 + l) / 2 = (a + b + l + 2) / 2 := by congr 1 <;> omega
  have hB2 : (a + b + 2 + l) / 2 = (a + b + l + 2) / 2 := by congr 1 <;> omega
  have hB3 : (a + b + b + a) / 2 = (a + a + b + b) / 2 := by congr 1 <;> omega
  have hrange : a + b + b + a + 2 + l = a + a + b + b + l + 2 := by omega
  simp [tetA, tetB, Fin.prod_univ_succ, hA1, hA2, hB1, hB2, hB3, hrange]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro S _
    simp [tetSummand, tetA, tetB, Fin.prod_univ_succ, hA1, hA2, hB1, hB2, hB3]
    ring

private lemma invalid (a b c d j l : ℤ)
    (hex : ¬ (hAdmissible a b c d j ∧ vAdmissible a b c d l)) :
    mainResidual a b c d j l = 0 := by
  by_cases hj : hAdmissible a b c d j
  · have hl : ¬vAdmissible a b c d l := fun hl => hex ⟨hj, hl⟩
    simp [mainResidual, normalizedTetSum, tetSum, hl]
  · simp [mainResidual, Lm2, diagonalEntry, Lp2, h, hj]

end TetExceptionalProof

theorem result (a b c d j l : ℤ)
    (hex : j = 0 ∨ ¬ (hAdmissible a b c d j ∧ vAdmissible a b c d l)) :
    mainResidual a b c d j l = 0 := by
  by_cases hadm : hAdmissible a b c d j ∧ vAdmissible a b c d l
  · have hz : j = 0 := hex.resolve_right (not_not.mpr hadm)
    subst j
    have hj := hadm.1
    have hl := hadm.2
    have hlabels : d = a ∧ c = b := by
      dsimp [hAdmissible, Admissible] at hj
      omega
    rcases hlabels with ⟨hd, hc⟩
    subst d
    subst c
    have hab : Admissible a b l := hl.1
    have ha : 0 ≤ a := hab.1
    have hb : 0 ≤ b := hab.2.1
    have hneg : ¬hAdmissible a b b a (0 - 2) := by
      dsimp [hAdmissible, Admissible]
      omega
    by_cases hapos : 0 < a
    · by_cases hbpos : 0 < b
      · have htwo : hAdmissible a b b a (0 + 2) := by
          constructor <;> dsimp [Admissible] <;> omega
        have ht := tet_special_evaluations.1 a b l hapos hbpos hab
        rw [← TetExceptionalProof.permute a b l hapos hbpos hab] at ht
        have ht0 := TetExceptionalProof.zero_edge a b l hab
        have hn0 := h_ne_zero a b b a 0 hj
        have hn2 := h_ne_zero a b b a (0 + 2) htwo
        norm_num at hn2
        have hguard : hAdmissible a b b a 0 ∧ hAdmissible a b b a (0 + 2) := ⟨hj, htwo⟩
        have hLm : Lm2 a b b a 0 = 0 := by
          unfold Lm2
          rw [if_neg (fun hbad => hneg hbad.2)]
        have hLc : diagonalEntry a b b a 0 = 0 := by
          simp [diagonalEntry]
        have hLu : Lp2 a b b a 0 = h a b b a 2 * ⟬a⟭ * ⟬b⟭ := by
          unfold Lp2
          rw [if_pos hguard]
          rw [show (a + a - 0) / 2 = a by omega,
            show (b + b - 0) / 2 = b by omega]
          norm_num
        simp only [mainResidual, hLm, hLc, hLu, normalizedTetSum,
          zero_mul, zero_add, zero_sub, ht0]
        field_simp [hn0, hn2]
        linear_combination ht
      · have hb0 : b = 0 := by omega
        subst b
        have hle : l = a := by dsimp [Admissible] at hab; omega
        subst l
        have htwo : ¬hAdmissible a 0 0 a (0 + 2) := by
          dsimp [hAdmissible, Admissible]
          omega
        norm_num at hneg htwo
        simp [mainResidual, Lm2, diagonalEntry, Lp2, hneg, htwo, Λ, qInt]
    · have ha0 : a = 0 := by omega
      subst a
      have hle : l = b := by dsimp [Admissible] at hab; omega
      subst l
      have htwo : ¬hAdmissible 0 b b 0 (0 + 2) := by
        dsimp [hAdmissible, Admissible]
        omega
      norm_num at hneg htwo
      simp [mainResidual, Lm2, diagonalEntry, Lp2, hneg, htwo, Λ, qInt]
  · exact TetExceptionalProof.invalid a b c d j l hadm

end PartTetExceptional
private def tet_exceptional := PartTetExceptional.result

open QuantumSixJ
open QuantumSixJ.Certificate
open scoped QuantumSixJ BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

private lemma local_telescope (A B C E F j S : ℤ) (hS : 0 ≤ S) :
    rawResidual A B C E F j S = flux A B C E F j (S + 1) - flux A B C E F j S := by
  obtain ⟨hm, h0, hp, hf, hn⟩ := tet_common_weight A B C E F j S hS
  have halg := tet_certificate_algebra A B C E F j S
  change
    lowerCoefficient A B j * ⟬E - S⟭ * ⟬F - S⟭ *
        (⟬E - S + 1⟭ * ⟬F - S + 1⟭) +
      centerCoefficient A B C E F j * (⟬S - A + 1⟭ * ⟬S - B + 1⟭) *
        (⟬E - S + 1⟭ * ⟬F - S + 1⟭) +
      upperCoefficient C E F j * ⟬S - A⟭ * ⟬S - B⟭ *
        (⟬S - A + 1⟭ * ⟬S - B + 1⟭) +
      ⟬S + 2⟭ * ⟬A + B - j - S⟭ * (⟬E - S + 1⟭ * ⟬F - S + 1⟭) *
        scaledMultiplier A B C E F j (S + 1) +
      ⟬S - C⟭ * ⟬S - (E + F - C - j)⟭ * (⟬S - A + 1⟭ * ⟬S - B + 1⟭) *
        scaledMultiplier A B C E F j S = 0 at halg
  dsimp only [rawResidual]
  rw [hm, h0, hp, hn, hf]
  linear_combination (commonWeight A B C E F j S) * halg

private lemma total_zero (a b c d j l : ℤ)
    (hj : hAdmissible a b c d j) (hl : vAdmissible a b c d l) (hpos : 0 < j) :
    totalResidual a b c d j l = 0 := by
  obtain ⟨h0, hn⟩ := tet_flux_endpoints a b c d j l hj hl hpos
  let A := tetA a b c d j l
  let B := tetB a b c d j l
  let f : ℕ → Scalar := fun k => flux (A 0) (A 1) (A 2) (B 0) (B 1) j (k : ℤ)
  change (∑ k ∈ Finset.range (sumLength a b c d j l),
    rawResidual (A 0) (A 1) (A 2) (B 0) (B 1) j (k : ℤ)) = 0
  calc
    _ = ∑ k ∈ Finset.range (sumLength a b c d j l), (f (k + 1) - f k) := by
      apply Finset.sum_congr rfl
      intro k _
      simpa [f, Nat.cast_add, Nat.cast_one] using
        local_telescope (A 0) (A 1) (A 2) (B 0) (B 1) j (k : ℤ) (by omega)
    _ = f (sumLength a b c d j l) - f 0 := Finset.sum_range_sub f _
    _ = 0 := by simpa [f, A, B, h0, hn]

private theorem scalar_recurrence (a b c d j l : ℤ) :
    Lm2 a b c d j * normalizedTetSum a b c d (j - 2) l +
      (diagonalEntry a b c d j - Λ a b l * h a b c d j) *
        normalizedTetSum a b c d j l +
      Lp2 a b c d j * normalizedTetSum a b c d (j + 2) l = 0 := by
  change mainResidual a b c d j l = 0
  by_cases hadm : hAdmissible a b c d j ∧ vAdmissible a b c d l
  · by_cases hz : j = 0
    · exact tet_exceptional a b c d j l (Or.inl hz)
    · have hj0 := hadm.1.1.2.2.1
      have hpos : 0 < j := by omega
      rw [tet_prefactor_match a b c d j l hadm.1 hadm.2 hpos,
        total_zero a b c d j l hadm.1 hadm.2 hpos, mul_zero]
  · exact tet_exceptional a b c d j l (Or.inr hadm)

private lemma matrix_diag (a b c d j : ℤ) :
    L a b c d j j = diagonalEntry a b c d j := by
  simp [L, diagonalEntry]

private lemma matrix_upper (a b c d j : ℤ) :
    L a b c d j (j + 2) = Lp2 a b c d j := by
  have hn : j ≠ j + 2 := by omega
  unfold L
  rw [if_neg hn, if_pos (show j + 2 = j + 2 ∨ j = j + 2 + 2 from Or.inl rfl)]
  dsimp only
  rw [min_eq_left (show j ≤ j + 2 by omega), max_eq_right (show j ≤ j + 2 by omega)]
  rfl

private lemma matrix_lower (a b c d j : ℤ) :
    L a b c d j (j - 2) = Lm2 a b c d j := by
  have hn : j ≠ j - 2 := by omega
  have he : j = j - 2 + 2 := by omega
  unfold L
  rw [if_neg hn, if_pos (Or.inr he : j - 2 = j + 2 ∨ j = j - 2 + 2)]
  dsimp only
  rw [min_eq_right (show j - 2 ≤ j by omega), max_eq_left (show j - 2 ≤ j by omega)]
  by_cases hj : hAdmissible a b c d j <;>
    by_cases hm : hAdmissible a b c d (j - 2) <;>
    simp only [Lm2, hj, hm, and_self, true_and, false_and,
      and_false, and_true, if_true, if_false] <;> rfl

theorem solution : QuantumSixJ.SumRecurrence := by
  intro a b c d j l
  rw [matrix_lower, matrix_diag, matrix_upper]
  exact scalar_recurrence a b c d j l
