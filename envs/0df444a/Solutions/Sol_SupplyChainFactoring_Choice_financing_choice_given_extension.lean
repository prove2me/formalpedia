-- Prove2me | solution 1 for SupplyChainFactoring.Choice.financing_choice_given_extension
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T05:30:31.662369+00:00
-- url     : https://prove2.me/submissions/cb15283a-6d79-44a8-b6a4-ba65446664c6

import Theorems.Thm_SupplyChainFactoring_Choice_recourse_equilibrium
import Theorems.Thm_SupplyChainFactoring_Choice_nonRecourse_equilibrium
import Theorems.Thm_SupplyChainFactoring_Choice_reverse_equilibrium
import Theorems.Thm_SupplyChainFactoring_Choice_supplier_preference_coef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open MeasureTheory Real
open SupplyChainFactoring.Choice

namespace FactoringReduction

private lemma rho_lt_one (P : Params) (hP : P.Valid) {C : ℝ}
    (hC : C ∈ Set.Ioo P.Cmin P.Cmax) : P.ρ C < 1 := by
  obtain ⟨a, ha, haC⟩ := exists_between hC.1
  exact lt_of_lt_of_le (hP.ρ_strictAnti ⟨ha, haC.trans hC.2⟩ hC haC)
    (hP.ρ_mem a ⟨ha, haC.trans hC.2⟩).2

private lemma coefF_strictMono (P : Params) (hP : P.Valid) (Cr : ℝ) :
    StrictMonoOn (fun Cs => coefF P Cs Cr) (Set.Ioo P.Cmin P.Cmax) := by
  intro a ha b hb hab
  have hr := hP.ρ_strictAnti ha hb hab
  have he := exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (hP.η_anti ha hb hab.le) hP.t2_pos.le)
  unfold coefF
  linarith

private lemma numerator_anti (P : Params) (hP : P.Valid) :
    AntitoneOn (fun Cs => P.c * exp ((P.η Cs + P.lamS) * P.t1))
      (Set.Ioo P.Cmin P.Cmax) := by
  intro a ha b hb hab
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (show P.η b + P.lamS ≤ P.η a + P.lamS by linarith [hP.η_anti ha hb hab]) hP.t1_pos.le))
    hP.c_pos.le

private lemma unique_anti_crossing {a b C v : ℝ} {g : ℝ → ℝ}
    (hg : AntitoneOn g (Set.Ioo a b))
    (hC : IsUniqueSolution a b (fun x => g x = v) C)
    {x : ℝ} (hx : x ∈ Set.Ioo a b) : g x < v ↔ C < x := by
  constructor
  · intro h
    by_contra hn
    have hh := hg hx hC.1 (le_of_not_gt hn)
    rw [hC.2.1] at hh
    exact (not_lt_of_ge hh) h
  · intro h
    have hh : g x ≤ v := hC.2.1 ▸ hg hC.1 hx h.le
    exact lt_of_le_of_ne hh (fun he => (ne_of_gt h) (hC.2.2 x hx he))

private lemma nonRecourse_crossing (P : Params) (hP : P.Valid) (Cr : ℝ)
    (hCr : Cr ∈ Set.Ioo P.Cmin P.Cmax) (CN : ℝ)
    (hCN : IsUniqueSolution P.Cmin P.Cmax (fun Cs => cN P Cs Cr = P.p) CN)
    {Cs : ℝ} (hCs : Cs ∈ Set.Ioo P.Cmin P.Cmax) :
    P.c * exp ((P.η Cs + P.lamS) * P.t1) < P.p * coefN P Cr ↔ CN < Cs := by
  have hr : 0 < 1 - P.ρ Cr := sub_pos.mpr (rho_lt_one P hP hCr)
  have he : ∀ x, cN P x Cr = P.p ↔
      P.c * exp ((P.η x + P.lamS) * P.t1) = P.p * coefN P Cr := by
    intro x
    unfold cN coefN
    rw [div_eq_iff hr.ne', exp_add, exp_neg]
    have hh :
        (P.c * exp ((P.η x + P.lamS) * P.t1)) * exp (P.η Cr * P.t2) =
            P.p * (1 - P.ρ Cr) ↔
        P.c * exp ((P.η x + P.lamS) * P.t1) =
            (P.p * (1 - P.ρ Cr)) / exp (P.η Cr * P.t2) :=
      (eq_div_iff (exp_pos (P.η Cr * P.t2)).ne').symm
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  exact unique_anti_crossing (numerator_anti P hP)
    ⟨hCN.1, (he CN).mp hCN.2.1, fun x hx h => hCN.2.2 x hx ((he x).mpr h)⟩ hCs

private lemma reverse_crossing (P : Params) (hP : P.Valid) (Cr τ CR : ℝ)
    (hCR : IsUniqueSolution P.Cmin P.Cmax (fun Cs => cR P Cs Cr τ = P.p) CR)
    {Cs : ℝ} (hCs : Cs ∈ Set.Ioo P.Cmin P.Cmax) :
    P.c * exp ((P.η Cs + P.lamS) * P.t1) < P.p * coefR P Cr τ ↔ CR < Cs := by
  have he : ∀ x, cR P x Cr τ = P.p ↔
      P.c * exp ((P.η x + P.lamS) * P.t1) = P.p * coefR P Cr τ := by
    intro x
    unfold cR coefR
    rw [exp_add, exp_neg]
    have hh :
        (P.c * exp ((P.η x + P.lamS) * P.t1)) * exp (P.η Cr * (P.t2 + τ)) = P.p ↔
        P.c * exp ((P.η x + P.lamS) * P.t1) = P.p / exp (P.η Cr * (P.t2 + τ)) :=
      (eq_div_iff (exp_pos (P.η Cr * (P.t2 + τ))).ne').symm
    simpa only [mul_assoc, div_eq_mul_inv] using hh
  exact unique_anti_crossing (numerator_anti P hP)
    ⟨hCR.1, (he CR).mp hCR.2.1, fun x hx h => hCR.2.2 x hx ((he x).mpr h)⟩ hCs

private lemma recourse_crossing (P : Params) (hP : P.Valid) (Cr CF : ℝ)
    (hCF : IsUniqueSolution P.Cmin P.Cmax
      (fun Cs => P.c * exp ((P.η Cs + P.lamS) * P.t1) = P.p * coefF P Cs Cr) CF)
    {Cs : ℝ} (hCs : Cs ∈ Set.Ioo P.Cmin P.Cmax) :
    P.c * exp ((P.η Cs + P.lamS) * P.t1) < P.p * coefF P Cs Cr ↔ CF < Cs := by
  have hp : 0 < P.p := hP.c_pos.trans hP.c_lt_p
  constructor
  · intro h
    by_contra hn
    have hn := le_of_not_gt hn
    have hnum := numerator_anti P hP hCs hCF.1 hn
    have hcoef := mul_le_mul_of_nonneg_left
      ((coefF_strictMono P hP Cr).monotoneOn hCs hCF.1 hn) hp.le
    linarith [hCF.2.1]
  · intro h
    have hnum := numerator_anti P hP hCF.1 hCs h.le
    have hcoef := mul_lt_mul_of_pos_left (coefF_strictMono P hP Cr hCF.1 hCs h) hp
    linarith [hCF.2.1]

private lemma scheme_forall (Q : Scheme → Prop) :
    (∀ i, Q i) ↔ Q .recourse ∧ Q .nonRecourse ∧ Q .reverse := by
  constructor
  · intro h
    exact ⟨h _, h _, h _⟩
  · rintro ⟨hF, hN, hR⟩ i
    cases i <;> assumption

private lemma adopted_coef_iff (P : Params) (μ : Measure ℝ) (Cs Cr τ : ℝ)
    (heq : ∀ i, Feasible P μ i Cs Cr τ → ∃ w q, IsEquilibrium P μ i Cs Cr τ w q)
    (hmono : ∀ i j, coef P i Cs Cr τ ≤ coef P j Cs Cr τ →
      Feasible P μ i Cs Cr τ → Feasible P μ j Cs Cr τ)
    (hcomp : ∀ i j, Feasible P μ i Cs Cr τ → Feasible P μ j Cs Cr τ →
      ∀ wi qi wj qj, IsEquilibrium P μ i Cs Cr τ wi qi →
      IsEquilibrium P μ j Cs Cr τ wj qj →
      (supplierProfit P μ i Cs Cr τ wi qi ≤ supplierProfit P μ j Cs Cr τ wj qj ↔
        coef P i Cs Cr τ ≤ coef P j Cs Cr τ) ∧
      (supplierProfit P μ i Cs Cr τ wi qi < supplierProfit P μ j Cs Cr τ wj qj ↔
        coef P i Cs Cr τ < coef P j Cs Cr τ)) (i : Scheme) :
    Adopted P μ Set.univ i Cs Cr τ ↔ Feasible P μ i Cs Cr τ ∧
      ∀ j, (j.rank < i.rank → coef P j Cs Cr τ ≤ coef P i Cs Cr τ) ∧
        (i.rank < j.rank → coef P j Cs Cr τ < coef P i Cs Cr τ) := by
  classical
  constructor
  · rintro ⟨_, hi, wi, qi, hei, hw⟩
    refine ⟨hi, fun j => ?_⟩
    by_cases hji : j = i
    · subst j
      simp only [lt_self_iff_false, false_implies, and_self]
    by_cases hj : Feasible P μ j Cs Cr τ
    · obtain ⟨wj, qj, hej⟩ := heq j hj
      have hh := hw j (Set.mem_univ _) hji hj wj qj hej
      have hc := hcomp j i hj hi wj qj wi qi hej hei
      exact ⟨fun h => hc.1.mp (hh.1 h), fun h => hc.2.mp (hh.2 h)⟩
    · have hc : coef P j Cs Cr τ < coef P i Cs Cr τ := by
        by_contra hn
        exact hj (hmono i j (le_of_not_gt hn) hi)
      exact ⟨fun _ => hc.le, fun _ => hc⟩
  · rintro ⟨hi, hcoef⟩
    obtain ⟨wi, qi, hei⟩ := heq i hi
    refine ⟨Set.mem_univ _, hi, wi, qi, hei, ?_⟩
    intro j _ _ hj wj qj hej
    have hc := hcomp j i hj hi wj qj wi qi hej hei
    exact ⟨fun h => hc.1.mpr ((hcoef j).1 h), fun h => hc.2.mpr ((hcoef j).2 h)⟩

end FactoringReduction

open FactoringReduction

theorem solution (P : Params) (hP : P.Valid) (μ : Measure ℝ) (f : ℝ → ℝ) (Z : EReal)
    (hD : DemandModel μ f Z) (Cr : ℝ) (hCr : Cr ∈ Set.Ioo P.Cmin P.Cmax)
    (τ : ℝ) (hτ : 0 ≤ τ) (CF : ℝ) (hCF : IsUniqueSolution P.Cmin P.Cmax
      (fun Cs => P.c * exp ((P.η Cs + P.lamS) * P.t1) = P.p * coefF P Cs Cr) CF)
    (CN : ℝ) (hCN : IsUniqueSolution P.Cmin P.Cmax (fun Cs => cN P Cs Cr = P.p) CN)
    (CR : ℝ) (hCR : IsUniqueSolution P.Cmin P.Cmax (fun Cs => cR P Cs Cr τ = P.p) CR)
    (C1 : ℝ) (hC1 : IsUniqueSolution P.Cmin P.Cmax (fun Cs => coefF P Cs Cr = coefN P Cr) C1)
    (C3 : ℝ) (hC3 : IsUniqueSolution P.Cmin P.Cmax (fun Cs => coefF P Cs Cr = coefR P Cr τ) C3) :
    ∀ Cs ∈ Set.Ioo P.Cmin P.Cmax,
      (exp (-(P.η Cr * τ)) < 1 - P.ρ Cr →
        (Adopted P μ Set.univ .recourse Cs Cr τ ↔ max CF C1 < Cs) ∧
        (Adopted P μ Set.univ .nonRecourse Cs Cr τ ↔ CN < Cs ∧ Cs ≤ C1)) ∧
      (1 - P.ρ Cr ≤ exp (-(P.η Cr * τ)) →
        (Adopted P μ Set.univ .recourse Cs Cr τ ↔ max CF C3 < Cs) ∧
        (Adopted P μ Set.univ .reverse Cs Cr τ ↔ CR < Cs ∧ Cs ≤ C3)) := by
  intro Cs hCs
  have hF := recourse_equilibrium P hP μ f Z hD Cr hCr τ CF hCF Cs hCs
  have hN := nonRecourse_equilibrium P hP μ f Z hD Cr hCr τ CN hCN Cs hCs
  have hR := reverse_equilibrium P hP μ f Z hD Cr hCr τ hτ CR hCR Cs hCs
  have hbudget : ∀ i, Feasible P μ i Cs Cr τ ↔
      P.c * exp ((P.η Cs + P.lamS) * P.t1) < P.p * coef P i Cs Cr τ := by
    intro i
    cases i with
    | recourse => exact hF.1.trans (recourse_crossing P hP Cr CF hCF hCs).symm
    | nonRecourse => exact hN.1.trans (nonRecourse_crossing P hP Cr hCr CN hCN hCs).symm
    | reverse => exact hR.1.trans (reverse_crossing P hP Cr τ CR hCR hCs).symm
  have heq : ∀ i, Feasible P μ i Cs Cr τ → ∃ w q, IsEquilibrium P μ i Cs Cr τ w q := by
    intro i hi
    have hh : ∃ e : ℝ × ℝ, IsEquilibrium P μ i Cs Cr τ e.1 e.2 := by
      cases i with
      | recourse => exact ((hF.2 (hF.1.mp hi)).1).exists
      | nonRecourse => exact ((hN.2 (hN.1.mp hi)).1).exists
      | reverse => exact ((hR.2 (hR.1.mp hi)).1).exists
    obtain ⟨⟨w, q⟩, hh⟩ := hh
    exact ⟨w, q, hh⟩
  have hmono : ∀ i j, coef P i Cs Cr τ ≤ coef P j Cs Cr τ →
      Feasible P μ i Cs Cr τ → Feasible P μ j Cs Cr τ := by
    intro i j hij hi
    exact (hbudget j).mpr ((hbudget i).mp hi |>.trans_le
      (mul_le_mul_of_nonneg_left hij (hP.c_pos.trans hP.c_lt_p).le))
  have hAd := adopted_coef_iff P μ Cs Cr τ heq hmono
    (supplier_preference_coef P hP μ f Z hD Cr hCr τ hτ Cs hCs)
  have hAF : Adopted P μ Set.univ .recourse Cs Cr τ ↔
      CF < Cs ∧ coefN P Cr < coefF P Cs Cr ∧ coefR P Cr τ < coefF P Cs Cr := by
    simpa only [scheme_forall, Scheme.rank, coef, Nat.lt_irrefl, Nat.zero_lt_succ,
      Nat.not_lt_zero, false_implies, true_implies, true_and, and_true, hF.1] using hAd .recourse
  have hAN : Adopted P μ Set.univ .nonRecourse Cs Cr τ ↔
      CN < Cs ∧ coefF P Cs Cr ≤ coefN P Cr ∧ coefR P Cr τ < coefN P Cr := by
    simpa only [scheme_forall, Scheme.rank, coef, Nat.lt_irrefl, Nat.zero_lt_succ,
      Nat.not_lt_zero, false_implies, true_implies, true_and, and_true, hN.1,
      show ¬ (2 : ℕ) < 1 by decide, show (1 : ℕ) < 2 by decide] using hAd .nonRecourse
  have hAR : Adopted P μ Set.univ .reverse Cs Cr τ ↔
      CR < Cs ∧ coefF P Cs Cr ≤ coefR P Cr τ ∧ coefN P Cr ≤ coefR P Cr τ := by
    simpa only [scheme_forall, Scheme.rank, coef, Nat.lt_irrefl, Nat.zero_lt_succ,
      Nat.not_lt_zero, false_implies, true_implies, true_and, and_true, hR.1,
      show ¬ (2 : ℕ) < 1 by decide, show (1 : ℕ) < 2 by decide] using hAd .reverse
  have hC1lt : coefN P Cr < coefF P Cs Cr ↔ C1 < Cs := by
    rw [← hC1.2.1]
    exact (coefF_strictMono P hP Cr).lt_iff_lt hC1.1 hCs
  have hC1le : coefF P Cs Cr ≤ coefN P Cr ↔ Cs ≤ C1 := by
    rw [← hC1.2.1]
    exact (coefF_strictMono P hP Cr).le_iff_le hCs hC1.1
  have hC3lt : coefR P Cr τ < coefF P Cs Cr ↔ C3 < Cs := by
    rw [← hC3.2.1]
    exact (coefF_strictMono P hP Cr).lt_iff_lt hC3.1 hCs
  have hC3le : coefF P Cs Cr ≤ coefR P Cr τ ↔ Cs ≤ C3 := by
    rw [← hC3.2.1]
    exact (coefF_strictMono P hP Cr).le_iff_le hCs hC3.1
  have hRexp : coefR P Cr τ = exp (-(P.η Cr * P.t2)) * exp (-(P.η Cr * τ)) := by
    unfold coefR
    rw [mul_add, neg_add, exp_add]
  constructor
  · intro hcase
    have hRN : coefR P Cr τ < coefN P Cr := by
      rw [hRexp, coefN]
      exact mul_lt_mul_of_pos_left hcase (exp_pos _)
    constructor
    · rw [hAF, max_lt_iff]
      constructor
      · rintro ⟨hCFs, hNFs, _⟩
        exact ⟨hCFs, hC1lt.mp hNFs⟩
      · rintro ⟨hCFs, hC1s⟩
        have hNFs := hC1lt.mpr hC1s
        exact ⟨hCFs, hNFs, hRN.trans hNFs⟩
    · rw [hAN, hC1le]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hRN⟩⟩
  · intro hcase
    have hNR : coefN P Cr ≤ coefR P Cr τ := by
      rw [hRexp, coefN]
      exact mul_le_mul_of_nonneg_left hcase (exp_pos _).le
    constructor
    · rw [hAF, max_lt_iff]
      constructor
      · rintro ⟨hCFs, _, hRFs⟩
        exact ⟨hCFs, hC3lt.mp hRFs⟩
      · rintro ⟨hCFs, hC3s⟩
        have hRFs := hC3lt.mpr hC3s
        exact ⟨hCFs, hNR.trans_lt hRFs, hRFs⟩
    · rw [hAR, hC3le]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hNR⟩⟩
