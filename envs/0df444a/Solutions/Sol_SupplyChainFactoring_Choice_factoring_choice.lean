-- Prove2me | solution 1 for SupplyChainFactoring.Choice.factoring_choice
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:28:47.712877+00:00
-- url     : https://prove2.me/submissions/113fe64c-a711-4585-9251-8ef9f79e658d

import Theorems.Thm_SupplyChainFactoring_Choice_recourse_equilibrium
import Theorems.Thm_SupplyChainFactoring_Choice_nonRecourse_equilibrium
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


end FactoringReduction

open FactoringReduction

theorem solution (P : Params) (hP : P.Valid) (μ : Measure ℝ) (f : ℝ → ℝ) (Z : EReal)
    (hD : DemandModel μ f Z) (Cr : ℝ) (hCr : Cr ∈ Set.Ioo P.Cmin P.Cmax)
    (τ : ℝ) (CF : ℝ) (hCF : IsUniqueSolution P.Cmin P.Cmax
      (fun Cs => P.c * exp ((P.η Cs + P.lamS) * P.t1) = P.p * coefF P Cs Cr) CF)
    (CN : ℝ) (hCN : IsUniqueSolution P.Cmin P.Cmax (fun Cs => cN P Cs Cr = P.p) CN)
    (C1 : ℝ) (hC1 : IsUniqueSolution P.Cmin P.Cmax (fun Cs => coefF P Cs Cr = coefN P Cr) C1) :
    ∀ Cs ∈ Set.Ioo P.Cmin P.Cmax,
      (Adopted P μ {Scheme.recourse, Scheme.nonRecourse} .nonRecourse Cs Cr τ ↔
          CN < Cs ∧ Cs ≤ C1) ∧
      (Adopted P μ {Scheme.recourse, Scheme.nonRecourse} .recourse Cs Cr τ ↔
          max CF C1 < Cs) := by
  intro Cs hCs
  have hF := recourse_equilibrium P hP μ f Z hD Cr hCr τ CF hCF Cs hCs
  have hN := nonRecourse_equilibrium P hP μ f Z hD Cr hCr τ CN hCN Cs hCs
  have hBF := hF.1.trans (recourse_crossing P hP Cr CF hCF hCs).symm
  have hBN := hN.1.trans (nonRecourse_crossing P hP Cr hCr CN hCN hCs).symm
  have hmonoFN : coefF P Cs Cr ≤ coefN P Cr →
      Feasible P μ .recourse Cs Cr τ → Feasible P μ .nonRecourse Cs Cr τ := by
    intro hcoef hf
    exact hBN.mpr ((hBF.mp hf).trans_le
      (mul_le_mul_of_nonneg_left hcoef (hP.c_pos.trans hP.c_lt_p).le))
  have hmonoNF : coefN P Cr ≤ coefF P Cs Cr →
      Feasible P μ .nonRecourse Cs Cr τ → Feasible P μ .recourse Cs Cr τ := by
    intro hcoef hn
    exact hBF.mpr ((hBN.mp hn).trans_le
      (mul_le_mul_of_nonneg_left hcoef (hP.c_pos.trans hP.c_lt_p).le))
  have hC1lt : coefN P Cr < coefF P Cs Cr ↔ C1 < Cs := by
    rw [← hC1.2.1]
    exact (coefF_strictMono P hP Cr).lt_iff_lt hC1.1 hCs
  have hC1le : coefF P Cs Cr ≤ coefN P Cr ↔ Cs ≤ C1 := by
    rw [← hC1.2.1]
    exact (coefF_strictMono P hP Cr).le_iff_le hCs hC1.1
  have hcomp := supplier_preference_coef P hP μ f Z hD Cr hCr 0 (le_refl 0) Cs hCs
  constructor
  · constructor
    · rintro ⟨_, hn, wn, qn, hen, hchoice⟩
      refine ⟨hN.1.mp hn, ?_⟩
      by_contra hnot
      have hcoef := hC1lt.mpr (lt_of_not_ge hnot)
      have hf := hmonoNF hcoef.le hn
      obtain ⟨⟨wf, qf⟩, hef, _⟩ := (hF.2 (hF.1.mp hf)).1
      have hh := (hchoice .recourse (by simp) (by decide) hf wf qf hef).1 (by decide)
      have hc := (hcomp .recourse .nonRecourse hf hn wf qf wn qn hef hen).1.mp hh
      exact not_lt_of_ge hc hcoef
    · rintro ⟨hCNs, hCs1⟩
      have hn := hN.1.mpr hCNs
      obtain ⟨⟨wn, qn⟩, hen, _⟩ := (hN.2 hCNs).1
      refine ⟨by simp, hn, wn, qn, hen, ?_⟩
      intro j hj hji hjf wj qj hej
      have hj : j = Scheme.recourse := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, or_iff_left hji] using hj
      subst j
      constructor
      · intro _
        exact (hcomp .recourse .nonRecourse hjf hn wj qj wn qn hej hen).1.mpr (hC1le.mpr hCs1)
      · intro hbad
        simp [Scheme.rank] at hbad
  · constructor
    · rintro ⟨_, hf, wf, qf, hef, hchoice⟩
      apply max_lt_iff.mpr
      refine ⟨hF.1.mp hf, ?_⟩
      by_contra hnot
      have hcoef := hC1le.mpr (le_of_not_gt hnot)
      have hn := hmonoFN hcoef hf
      obtain ⟨⟨wn, qn⟩, hen, _⟩ := (hN.2 (hN.1.mp hn)).1
      have hh := (hchoice .nonRecourse (by simp) (by decide) hn wn qn hen).2 (by decide)
      have hc := (hcomp .nonRecourse .recourse hn hf wn qn wf qf hen hef).2.mp hh
      exact not_lt_of_ge hcoef hc
    · intro h
      obtain ⟨hCFs, hC1s⟩ := max_lt_iff.mp h
      have hf := hF.1.mpr hCFs
      obtain ⟨⟨wf, qf⟩, hef, _⟩ := (hF.2 hCFs).1
      refine ⟨by simp, hf, wf, qf, hef, ?_⟩
      intro j hj hji hjf wj qj hej
      have hj : j = Scheme.nonRecourse := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, or_iff_right hji] using hj
      subst j
      constructor
      · intro hbad
        simp [Scheme.rank] at hbad
      · intro _
        exact (hcomp .nonRecourse .recourse hjf hf wj qj wf qf hej hef).2.mpr (hC1lt.mpr hC1s)
