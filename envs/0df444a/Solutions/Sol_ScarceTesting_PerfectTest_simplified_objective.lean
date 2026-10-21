-- Prove2me | solution 1 for ScarceTesting.PerfectTest.simplified_objective
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:09:58.164924+00:00
-- url     : https://prove2.me/submissions/50c4e977-bae6-4ffe-8c18-bf3b8e13086c

import Definitions.Def_ScarceTesting_PerfectTest_Setting

set_option autoImplicit false
open MeasureTheory Set Topology ScarceTesting.PerfectTest

lemma key6 (a b : ℝ) (h : ¬ (a < 0 ∧ 0 < b)) :
    0 < max 0 a + max 0 b - max 0 (a + b) ↔ 0 < a ∧ b < 0 := by
  simp only [max_def]
  split_ifs <;> constructor <;> intro h' <;>
    first
    | (exfalso; linarith)
    | exact ⟨by linarith, by linarith⟩
    | (exfalso; apply h; exact ⟨by linarith, by linarith⟩)
    | linarith

lemma thr_facts (c φ σ : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (hφ0 : 0 ≤ φ) (hφσ : φ ≤ σ) (hσ1 : σ ≤ 1)
    (hσ0 : 0 < σ) (hφ1 : φ < 1) :
    0 < c * φ + (1 - c) * σ ∧ 0 < c * (1 - φ) + (1 - c) * (1 - σ) ∧
    0 ≤ tL c φ σ ∧ tL c φ σ ≤ c ∧ c ≤ tH c φ σ ∧ tH c φ σ ≤ 1 := by
  have h1c : 0 < 1 - c := by linarith
  have h1φ : 0 < 1 - φ := by linarith
  have hDL : 0 < c * φ + (1 - c) * σ := by positivity
  have hDH : 0 < c * (1 - φ) + (1 - c) * (1 - σ) := by
    have : 0 ≤ (1 - c) * (1 - σ) := mul_nonneg h1c.le (by linarith)
    have : 0 < c * (1 - φ) := by positivity
    linarith
  refine ⟨hDL, hDH, ?_, ?_, ?_, ?_⟩
  · unfold tL; positivity
  · unfold tL; rw [div_le_iff₀ hDL]
    nlinarith [mul_nonneg (mul_nonneg hc0.le h1c.le) (sub_nonneg.2 hφσ)]
  · unfold tH; rw [le_div_iff₀ hDH]
    nlinarith [mul_nonneg (mul_nonneg hc0.le h1c.le) (sub_nonneg.2 hφσ)]
  · unfold tH
    rw [div_le_one hDH]
    nlinarith [mul_nonneg h1c.le (sub_nonneg.2 hσ1)]

lemma V_iff (c φ σ μ : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (hφ0 : 0 ≤ φ) (hφσ : φ ≤ σ) (hσ1 : σ ≤ 1)
    (hσ0 : 0 < σ) (hφ1 : φ < 1) :
    0 < Vtest c φ σ μ ↔ tL c φ σ < μ ∧ μ < tH c φ σ := by
  obtain ⟨hDL, hDH, hL0, hLc', hcH', hH1⟩ := thr_facts c φ σ hc0 hc1 hφ0 hφσ hσ1 hσ0 hφ1
  have h1c : 0 < 1 - c := by linarith
  have h1φ : 0 < 1 - φ := by linarith
  have hLiff : tL c φ σ < μ ↔ 0 < μ * σ - c * (μ * σ + (1 - μ) * φ) := by
    unfold tL
    rw [div_lt_iff₀ hDL]
    constructor <;> intro h <;> nlinarith
  have hHiff : μ < tH c φ σ ↔ μ * (1 - σ) - c * (μ * (1 - σ) + (1 - μ) * (1 - φ)) < 0 := by
    unfold tH
    rw [lt_div_iff₀ hDH]
    constructor <;> intro h <;> nlinarith
  rw [hLiff, hHiff]
  unfold Vtest Utest UnoTest
  have hs : μ - c = (μ * σ - c * (μ * σ + (1 - μ) * φ)) +
      (μ * (1 - σ) - c * (μ * (1 - σ) + (1 - μ) * (1 - φ))) := by ring
  rw [hs]
  rw [← key6]
  · rintro ⟨ha, hb⟩
    have h1 : μ < tL c φ σ := by
      unfold tL; rw [lt_div_iff₀ hDL]; nlinarith
    have h2 : tH c φ σ < μ := by
      unfold tH; rw [div_lt_iff₀ hDH]; nlinarith
    linarith

lemma hsub (f : ℝ → ℝ) (hf : IsPriorDensity f) (a b : ℝ) (ha : a ∈ Icc (0:ℝ) 1)
    (hb : b ∈ Icc (0:ℝ) 1) : IntervalIntegrable f volume a b := by
  refine hf.integrable.mono_set ?_
  rw [uIcc_of_le zero_le_one]
  exact uIcc_subset_Icc ha hb

lemma demand_eq (f : ℝ → ℝ) (c φ σ : ℝ) (hf : IsPriorDensity f)
    (hc0 : 0 < c) (hc1 : c < 1) (hφ0 : 0 ≤ φ) (hφσ : φ ≤ σ) (hσ1 : σ ≤ 1)
    (hσ0 : 0 < σ) (hφ1 : φ < 1) :
    demand f c φ σ = cdf f (tH c φ σ) - cdf f (tL c φ σ) := by
  obtain ⟨hDL, hDH, hL0, hLc', hcH', hH1⟩ := thr_facts c φ σ hc0 hc1 hφ0 hφσ hσ1 hσ0 hφ1
  have hLH : tL c φ σ ≤ tH c φ σ := hLc'.trans hcH'
  have hreq : requestSet c φ σ = Ioo (tL c φ σ) (tH c φ σ) := by
    ext μ
    simp only [requestSet, mem_setOf_eq, mem_Ioo, mem_Icc]
    have hV := V_iff c φ σ μ hc0 hc1 hφ0 hφσ hσ1 hσ0 hφ1
    constructor
    · rintro ⟨_, h⟩; exact hV.1 h
    · intro h
      exact ⟨⟨hL0.trans h.1.le, h.2.le.trans hH1⟩, hV.2 h⟩
  unfold demand
  rw [hreq, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hLH]
  unfold cdf
  rw [intervalIntegral.integral_interval_sub_left
    (hsub f hf _ _ ⟨le_rfl, zero_le_one⟩ ⟨hL0.trans hLH, hH1⟩ |> fun _ => hsub f hf 0 _ ⟨le_rfl, zero_le_one⟩ ⟨hL0.trans hLH, hH1⟩)
    (hsub f hf 0 _ ⟨le_rfl, zero_le_one⟩ ⟨hL0, hLH.trans hH1⟩)]
lemma ii_congr (g h : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hh : IntervalIntegrable h volume a b)
    (heq : EqOn g h (Ioo a b)) : IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab] at hh ⊢
  exact hh.congr_fun (fun x hx => (heq hx).symm) measurableSet_Ioo

lemma int_congr (g h : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (heq : EqOn g h (Ioo a b)) :
    ∫ x in a..b, g x = ∫ x in a..b, h x :=
  intervalIntegral.integral_congr_uIoo (by rwa [uIoo_of_le hab])

theorem solution (f : ℝ → ℝ) (c β κ φ σ : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (hφ0 : 0 ≤ φ) (hφσ : φ ≤ σ) (hσ1 : σ ≤ 1)
    (hσ0 : 0 < σ) (hφ1 : φ < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hf : IsPriorDensity f) :
    S f c β κ φ σ =
      (∫ μ in c..1, (μ - β * (1 - μ)) * f μ) +
      (∫ μ in c..tH c φ σ, availThr f κ (tL c φ σ) (tH c φ σ) *
          ((1 - μ) * β * (1 - φ) - μ * (1 - σ)) * f μ) +
      (∫ μ in tL c φ σ..c, availThr f κ (tL c φ σ) (tH c φ σ) *
          (μ * σ - (1 - μ) * β * φ) * f μ) := by
  obtain ⟨hDL, hDH, hL0, hLc, hcH, hH1⟩ := thr_facts c φ σ hc0 hc1 hφ0 hφσ hσ1 hσ0 hφ1
  have hV := V_iff c φ σ
  have hdem := demand_eq f c φ σ hf hc0 hc1 hφ0 hφσ hσ1 hσ0 hφ1
  set t1 := tL c φ σ with ht1
  set t2 := tH c φ σ with ht2
  set A := availThr f κ t1 t2 with hA
  have hAv : availability κ (demand f c φ σ) = A := by rw [hA, availThr, hdem]
  have hpay : ∀ μ, agentPayoff f c β κ φ σ μ =
      if t1 < μ ∧ μ < t2 then A * (μ * σ - β * (1 - μ) * φ) + (1 - A) * untestedPayoff c β μ
      else untestedPayoff c β μ := by
    intro μ
    unfold agentPayoff
    rw [hAv]
    by_cases h : t1 < μ ∧ μ < t2
    · rw [if_pos ((hV μ hc0 hc1 hφ0 hφσ hσ1 hσ0 hφ1).2 h), if_pos h]
    · rw [if_neg (fun h' => h ((hV μ hc0 hc1 hφ0 hφσ hσ1 hσ0 hφ1).1 h')), if_neg h]
  have h01 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have m1 : t1 ∈ Icc (0:ℝ) 1 := ⟨hL0, (hLc.trans hcH).trans hH1⟩
  have mc : c ∈ Icc (0:ℝ) 1 := ⟨hc0.le, hc1.le⟩
  have m2 : t2 ∈ Icc (0:ℝ) 1 := ⟨hL0.trans (hLc.trans hcH), hH1⟩
  have m3 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hLH : t1 ≤ t2 := hLc.trans hcH
  have hfi := hsub f hf
  -- integrands on the four pieces
  set g : ℝ → ℝ := fun μ => agentPayoff f c β κ φ σ μ * f μ with hg
  set h2 : ℝ → ℝ := fun μ => A * (μ * σ - (1 - μ) * β * φ) * f μ with hh2
  set h3 : ℝ → ℝ := fun μ => (A * (μ * σ - β * (1 - μ) * φ) + (1 - A) * (μ - β * (1 - μ))) * f μ
    with hh3
  set h4 : ℝ → ℝ := fun μ => (μ - β * (1 - μ)) * f μ with hh4
  have i2 : IntervalIntegrable h2 volume t1 c := by
    have := (hfi t1 c m1 mc).continuousOn_mul
      (g := fun μ => A * (μ * σ - (1 - μ) * β * φ)) (by fun_prop)
    exact this
  have i3 : IntervalIntegrable h3 volume c t2 := by
    have := (hfi c t2 mc m2).continuousOn_mul
      (g := fun μ => (A * (μ * σ - β * (1 - μ) * φ) + (1 - A) * (μ - β * (1 - μ)))) (by fun_prop)
    exact this
  have i4 : IntervalIntegrable h4 volume t2 1 := by
    have := (hfi t2 1 m2 m3).continuousOn_mul
      (g := fun μ => (μ - β * (1 - μ))) (by fun_prop)
    exact this
  have i0 : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume 0 t1 := intervalIntegrable_const
  have e1 : EqOn g (fun _ => (0:ℝ)) (Ioo 0 t1) := by
    intro μ hμ
    simp only [hg, hpay, untestedPayoff]
    rw [if_neg (fun h => by linarith [h.1, hμ.2]), if_neg (by intro h; linarith [hμ.2])]
    simp
  have e2 : EqOn g h2 (Ioo t1 c) := by
    intro μ hμ
    simp only [hg, hh2, hpay, untestedPayoff]
    rw [if_pos ⟨hμ.1, by linarith [hμ.2]⟩, if_neg (by intro h; linarith [hμ.2])]
    ring
  have e3 : EqOn g h3 (Ioo c t2) := by
    intro μ hμ
    simp only [hg, hh3, hpay, untestedPayoff]
    rw [if_pos ⟨by linarith [hμ.1], hμ.2⟩, if_pos hμ.1.le]
  have e4 : EqOn g h4 (Ioo t2 1) := by
    intro μ hμ
    simp only [hg, hh4, hpay, untestedPayoff]
    rw [if_neg (fun h => by linarith [h.2, hμ.1]), if_pos (by linarith [hμ.1])]
  have g0 := ii_congr g _ 0 t1 hL0 i0 e1
  have g2 := ii_congr g _ t1 c hLc i2 e2
  have g3 := ii_congr g _ c t2 hcH i3 e3
  have g4 := ii_congr g _ t2 1 hH1 i4 e4
  have hS : S f c β κ φ σ = ∫ μ in (0:ℝ)..1, g μ := rfl
  rw [hS, ← intervalIntegral.integral_add_adjacent_intervals g0 (g2.trans (g3.trans g4)),
    ← intervalIntegral.integral_add_adjacent_intervals g2 (g3.trans g4),
    ← intervalIntegral.integral_add_adjacent_intervals g3 g4,
    int_congr g _ 0 t1 hL0 e1, int_congr g _ t1 c hLc e2, int_congr g _ c t2 hcH e3,
    int_congr g _ t2 1 hH1 e4]
  -- right-hand side
  have r1 : (∫ μ in c..1, (μ - β * (1 - μ)) * f μ) =
      (∫ μ in c..t2, (μ - β * (1 - μ)) * f μ) + ∫ μ in t2..1, (μ - β * (1 - μ)) * f μ := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (((hfi c t2 mc m2).continuousOn_mul (g := fun μ => (μ - β * (1 - μ))) (by fun_prop)))
      i4]
  have ia : IntervalIntegrable (fun μ => (μ - β * (1 - μ)) * f μ) volume c t2 :=
    (hfi c t2 mc m2).continuousOn_mul (g := fun μ => (μ - β * (1 - μ))) (by fun_prop)
  have ib : IntervalIntegrable
      (fun μ => A * ((1 - μ) * β * (1 - φ) - μ * (1 - σ)) * f μ) volume c t2 :=
    (hfi c t2 mc m2).continuousOn_mul
      (g := fun μ => A * ((1 - μ) * β * (1 - φ) - μ * (1 - σ))) (by fun_prop)
  have r2 : (∫ μ in c..t2, h3 μ) = (∫ μ in c..t2, (μ - β * (1 - μ)) * f μ) +
      ∫ μ in c..t2, A * ((1 - μ) * β * (1 - φ) - μ * (1 - σ)) * f μ := by
    rw [← intervalIntegral.integral_add ia ib]
    refine intervalIntegral.integral_congr (fun μ _ => ?_)
    simp only [hh3]
    ring
  rw [r1, r2]
  simp only [hh4, hh2, intervalIntegral.integral_zero]
  linarith
