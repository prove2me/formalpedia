-- Prove2me | solution 1 for ScarceTesting.PerfectTest.proposition_2_i
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:22:45.135021+00:00
-- url     : https://prove2.me/submissions/8190e9a1-62ef-4b7f-8fb1-00300ef03391

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

lemma simp_obj (f : ℝ → ℝ) (c β κ φ σ : ℝ)
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

lemma wint (f : ℝ → ℝ) (hf : IsPriorDensity f) (w : ℝ → ℝ) (hw : Continuous w) (a b : ℝ)
    (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    IntervalIntegrable (fun x => w x * f x) volume a b :=
  (hsub f hf a b ha hb).continuousOn_mul hw.continuousOn

lemma tH_one (c φ : ℝ) (hc0 : 0 < c) (hφ : φ < 1) : tH c φ 1 = 1 := by
  have : 0 < 1 - φ := by linarith
  unfold tH
  have h : c * (1 - φ) ≠ 0 := by positivity
  simp [h]

lemma tL_nonneg (c φ : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hφ : 0 ≤ φ) : 0 ≤ tL c φ 1 := by
  unfold tL
  have : 0 < 1 - c := by linarith
  positivity

/-- right derivative at `0` of `u ↦ ∫_0^u g` -/
lemma ftc0 (g : ℝ → ℝ) (hi : IntervalIntegrable g volume 0 1)
    (hc : ContinuousWithinAt g (Icc 0 1) 0) :
    HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, g x) (g 0) (Ici 0) 0 := by
  have hIoo : Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT zero_lt_one
  have hIcc : Icc (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Filter.mem_of_superset hIoo Ioo_subset_Icc_self
  have hint : IntegrableOn g (Icc 0 1) volume := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one] at hi
    exact hi
  have hmeas : StronglyMeasurableAtFilter g (𝓝[>] (0:ℝ)) volume :=
    ⟨Icc 0 1, hIcc, hint.aestronglyMeasurable⟩
  have hcont : ContinuousWithinAt g (Ioi 0) 0 := hc.mono_of_mem_nhdsWithin hIcc
  exact intervalIntegral.integral_hasDerivWithinAt_right (s := Ici 0) (t := Ioi 0)
      (IntervalIntegrable.refl) hmeas hcont

/-- left derivative at `1` of `u ↦ ∫_0^u g` -/
lemma ftc1 (g : ℝ → ℝ) (hi : IntervalIntegrable g volume 0 1)
    (hc : ContinuousWithinAt g (Icc 0 1) 1) :
    HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, g x) (g 1) (Iic 1) 1 := by
  have hIcc : Icc (0:ℝ) 1 ∈ 𝓝[≤] (1:ℝ) := Icc_mem_nhdsLE zero_lt_one
  have hint : IntegrableOn g (Icc 0 1) volume := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one] at hi
    exact hi
  have hmeas : StronglyMeasurableAtFilter g (𝓝[≤] (1:ℝ)) volume :=
    ⟨Icc 0 1, hIcc, hint.aestronglyMeasurable⟩
  have hcont : ContinuousWithinAt g (Iic 1) 1 := hc.mono_of_mem_nhdsWithin hIcc
  exact intervalIntegral.integral_hasDerivWithinAt_right (s := Iic 1) (t := Iic 1) hi hmeas hcont

lemma diff_int (g : ℝ → ℝ) (hg : ∀ a b : ℝ, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
    IntervalIntegrable g volume a b) (a b : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    ∫ x in a..b, g x = (∫ x in (0:ℝ)..b, g x) - ∫ x in (0:ℝ)..a, g x := by
  rw [intervalIntegral.integral_interval_sub_left
    (hg 0 b ⟨le_rfl, zero_le_one⟩ hb) (hg 0 a ⟨le_rfl, zero_le_one⟩ ha)]

lemma avail_eq (f : ℝ → ℝ) (κ a b : ℝ) (h : κ < cdf f b - cdf f a) :
    availThr f κ a b = κ / (cdf f b - cdf f a) := by
  unfold availThr availability
  rw [if_neg (not_le.2 h)]

lemma wM (f : ℝ → ℝ) (hf : IsPriorDensity f) : ∀ a b : ℝ, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
    IntervalIntegrable (fun μ => μ * f μ) volume a b :=
  fun a b ha hb => wint f hf (fun x => x) continuous_id a b ha hb

lemma wN (f : ℝ → ℝ) (hf : IsPriorDensity f) : ∀ a b : ℝ, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
    IntervalIntegrable (fun μ => (1 - μ) * f μ) volume a b :=
  fun a b ha hb => wint f hf (fun x => 1 - x) (by fun_prop) a b ha hb

/-- formula for `S(φ,1)` -/
lemma S_phi (f : ℝ → ℝ) (hf : IsPriorDensity f) (c β κ φ : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hG : κ < cdf f 1 - cdf f (tL c φ 1)) :
    S f c β κ φ 1 = (∫ μ in c..1, (μ - β * (1 - μ)) * f μ) +
      κ / (cdf f 1 - cdf f (tL c φ 1)) *
        (β * (1 - φ) * (∫ μ in c..1, (1 - μ) * f μ) +
          ((∫ μ in (0:ℝ)..c, μ * f μ) - ∫ μ in (0:ℝ)..tL c φ 1, μ * f μ) -
          β * φ * ((∫ μ in (0:ℝ)..c, (1 - μ) * f μ) - ∫ μ in (0:ℝ)..tL c φ 1, (1 - μ) * f μ)) := by
  have h := simp_obj f c β κ φ 1 hc0 hc1 hφ0 hφ1.le le_rfl one_pos hφ1 hβ0 hβ1 hκ0 hκ1 hf
  rw [tH_one c φ hc0 hφ1] at h
  rw [h]
  have hL0 := tL_nonneg c φ hc0 hc1 hφ0
  have hLc : tL c φ 1 ≤ c :=
    (thr_facts c φ 1 hc0 hc1 hφ0 hφ1.le le_rfl one_pos hφ1).2.2.2.1
  have hAv := avail_eq f κ (tL c φ 1) 1 hG
  rw [hAv]
  set t1 := tL c φ 1 with ht1
  set A := κ / (cdf f 1 - cdf f t1) with hA
  have m1 : t1 ∈ Icc (0:ℝ) 1 := ⟨hL0, hLc.trans hc1.le⟩
  have mc : c ∈ Icc (0:ℝ) 1 := ⟨hc0.le, hc1.le⟩
  have m3 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have e2 : ∫ μ in c..1, A * ((1 - μ) * β * (1 - φ) - μ * (1 - 1)) * f μ =
      A * (β * (1 - φ)) * ∫ μ in c..1, (1 - μ) * f μ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun μ _ => ?_)
    simp only [sub_self, mul_zero, sub_zero]
    ring
  have a1 : ∫ μ in t1..c, μ * f μ = (∫ μ in (0:ℝ)..c, μ * f μ) - ∫ μ in (0:ℝ)..t1, μ * f μ :=
    diff_int (fun μ => μ * f μ) (wM f hf) t1 c m1 mc
  have a2 : ∫ μ in t1..c, (1 - μ) * f μ =
      (∫ μ in (0:ℝ)..c, (1 - μ) * f μ) - ∫ μ in (0:ℝ)..t1, (1 - μ) * f μ :=
    diff_int (fun μ => (1 - μ) * f μ) (wN f hf) t1 c m1 mc
  have e3 : ∫ μ in t1..c, A * (μ * 1 - (1 - μ) * β * φ) * f μ =
      A * ((∫ μ in t1..c, μ * f μ) - β * φ * ∫ μ in t1..c, (1 - μ) * f μ) := by
    have : (fun μ => A * (μ * 1 - (1 - μ) * β * φ) * f μ) =
        fun μ => A * (μ * f μ) - A * (β * φ) * ((1 - μ) * f μ) := by
      funext μ; ring
    rw [this, intervalIntegral.integral_sub
      ((wM f hf t1 c m1 mc).const_mul A) ((wN f hf t1 c m1 mc).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  rw [e2, e3, a1, a2]
  ring

lemma tL_zero (c σ : ℝ) : tL c 0 σ = 0 := by simp [tL]

lemma tH_zero_eq (c σ : ℝ) : tH c 0 σ = c / (1 - (1 - c) * σ) := by
  unfold tH; congr 1 <;> ring

lemma tH_zero_le (c σ : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hσ : σ ≤ 1) : tH c 0 σ ≤ 1 := by
  rw [tH_zero_eq]
  have : 0 < 1 - (1 - c) * σ := by nlinarith
  rw [div_le_one this]
  nlinarith

lemma tH_zero_nonneg (c σ : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hσ : σ ≤ 1) : 0 ≤ tH c 0 σ := by
  rw [tH_zero_eq]
  have : 0 < 1 - (1 - c) * σ := by nlinarith
  positivity

/-- formula for `S(0,σ)` -/
lemma S_sigma (f : ℝ → ℝ) (hf : IsPriorDensity f) (c β κ σ : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hG : κ < cdf f (tH c 0 σ) - cdf f 0) :
    S f c β κ 0 σ = (∫ μ in c..1, (μ - β * (1 - μ)) * f μ) +
      κ / (cdf f (tH c 0 σ) - cdf f 0) *
        (β * ((∫ μ in (0:ℝ)..tH c 0 σ, (1 - μ) * f μ) - ∫ μ in (0:ℝ)..c, (1 - μ) * f μ) -
          (1 - σ) * ((∫ μ in (0:ℝ)..tH c 0 σ, μ * f μ) - ∫ μ in (0:ℝ)..c, μ * f μ) +
          σ * ∫ μ in (0:ℝ)..c, μ * f μ) := by
  have h := simp_obj f c β κ 0 σ hc0 hc1 le_rfl hσ0.le hσ1 hσ0 zero_lt_one hβ0 hβ1 hκ0 hκ1 hf
  rw [tL_zero] at h
  rw [h]
  have hL0 := tH_zero_nonneg c σ hc0 hc1 hσ1
  have hH1 := tH_zero_le c σ hc0 hc1 hσ1
  have hcH := (thr_facts c 0 σ hc0 hc1 le_rfl hσ0.le hσ1 hσ0 zero_lt_one).2.2.2.2.1
  have hAv := avail_eq f κ 0 (tH c 0 σ) hG
  rw [hAv]
  set t2 := tH c 0 σ with ht2
  set A := κ / (cdf f t2 - cdf f 0) with hA
  have m2 : t2 ∈ Icc (0:ℝ) 1 := ⟨hL0, hH1⟩
  have mc : c ∈ Icc (0:ℝ) 1 := ⟨hc0.le, hc1.le⟩
  have m0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have a1 : ∫ μ in c..t2, μ * f μ = (∫ μ in (0:ℝ)..t2, μ * f μ) - ∫ μ in (0:ℝ)..c, μ * f μ :=
    diff_int (fun μ => μ * f μ) (wM f hf) c t2 mc m2
  have a2 : ∫ μ in c..t2, (1 - μ) * f μ =
      (∫ μ in (0:ℝ)..t2, (1 - μ) * f μ) - ∫ μ in (0:ℝ)..c, (1 - μ) * f μ :=
    diff_int (fun μ => (1 - μ) * f μ) (wN f hf) c t2 mc m2
  have e2 : ∫ μ in c..t2, A * ((1 - μ) * β * (1 - 0) - μ * (1 - σ)) * f μ =
      A * (β * (∫ μ in c..t2, (1 - μ) * f μ) - (1 - σ) * ∫ μ in c..t2, μ * f μ) := by
    have : (fun μ => A * ((1 - μ) * β * (1 - 0) - μ * (1 - σ)) * f μ) =
        fun μ => A * β * ((1 - μ) * f μ) - A * (1 - σ) * (μ * f μ) := by
      funext μ; ring
    rw [this, intervalIntegral.integral_sub
      ((wN f hf c t2 mc m2).const_mul _) ((wM f hf c t2 mc m2).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  have e3 : ∫ μ in (0:ℝ)..c, A * (μ * σ - (1 - μ) * β * 0) * f μ =
      A * (σ * ∫ μ in (0:ℝ)..c, μ * f μ) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun μ _ => ?_)
    simp only [mul_zero, sub_zero]
    ring
  rw [e2, e3, a1, a2]
  ring

lemma dS_dphi_aux (f : ℝ → ℝ) (c β κ : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hf : IsPriorDensity f) (hf0 : ContinuousWithinAt f (Set.Icc 0 1) 0) :
    HasDerivWithinAt (fun φ => S f c β κ φ 1)
      (-κ * β * (∫ μ in (0:ℝ)..1, (1 - μ) * f μ) +
        c / (1 - c) * κ * f 0 * (β * (∫ μ in c..1, (1 - μ) * f μ) + ∫ μ in (0:ℝ)..c, μ * f μ))
      (Set.Ici 0) 0 := by
  have h1c : 0 < 1 - c := by linarith
  have hi := hf.integrable
  have iM : IntervalIntegrable (fun μ => μ * f μ) volume 0 1 :=
    wM f hf 0 1 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  have iN : IntervalIntegrable (fun μ => (1 - μ) * f μ) volume 0 1 :=
    wN f hf 0 1 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  have hF0 : HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, f x) (f 0) (Ici 0) 0 := ftc0 f hi hf0
  have hM0 : HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, x * f x) (0 * f 0) (Ici 0) 0 :=
    ftc0 (fun x => x * f x) iM (continuousWithinAt_id.mul hf0)
  have hN0 : HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, (1 - x) * f x) ((1 - 0) * f 0)
      (Ici 0) 0 :=
    ftc0 (fun x => (1 - x) * f x) iN ((continuousWithinAt_const.sub continuousWithinAt_id).mul hf0)
  -- the threshold t_L(φ)
  have hT : HasDerivWithinAt (fun φ => tL c φ 1) (c / (1 - c)) (Ici 0) 0 := by
    have : HasDerivAt (fun φ : ℝ => c * φ / (c * φ + (1 - c))) (c / (1 - c)) 0 := by
      have h1 : HasDerivAt (fun φ : ℝ => c * φ) c 0 := by
        simpa using (hasDerivAt_id (0:ℝ)).const_mul c
      have h2 : HasDerivAt (fun φ : ℝ => c * φ + (1 - c)) c 0 := h1.add_const _
      have := h1.div h2 (by simp; linarith)
      refine HasDerivAt.congr_deriv this ?_
      have e : c * 0 + (1 - c) = 1 - c := by ring
      rw [e]
      have hc : (1 - c) ≠ 0 := h1c.ne'
      field_simp
      ring
    have e : (fun φ : ℝ => tL c φ 1) = fun φ => c * φ / (c * φ + (1 - c)) := by
      funext φ; simp [tL]
    rw [e]
    exact this.hasDerivWithinAt
  have hT0 : tL c 0 1 = 0 := by simp [tL]
  have hmaps : MapsTo (fun φ => tL c φ 1) (Ici 0) (Ici 0) :=
    fun φ hφ => tL_nonneg c φ hc0 hc1 hφ
  have hF0' : HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, f x) (f 0) (Ici 0)
      ((fun φ => tL c φ 1) 0) := by simpa only [hT0] using hF0
  have hM0' : HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, x * f x) (0 * f 0) (Ici 0)
      ((fun φ => tL c φ 1) 0) := by simpa only [hT0] using hM0
  have hN0' : HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, (1 - x) * f x) ((1 - 0) * f 0) (Ici 0)
      ((fun φ => tL c φ 1) 0) := by simpa only [hT0] using hN0
  have hFt := hF0'.scomp (0:ℝ) hT hmaps
  have hMt := hM0'.scomp (0:ℝ) hT hmaps
  have hNt := hN0'.scomp (0:ℝ) hT hmaps
  simp only [smul_eq_mul] at hFt hMt hNt
  -- constants
  set δ : ℝ := ∫ μ in c..1, (1 - μ) * f μ with hδ
  set Mc : ℝ := ∫ μ in (0:ℝ)..c, μ * f μ with hMc
  set Nc : ℝ := ∫ μ in (0:ℝ)..c, (1 - μ) * f μ with hNc
  set F1 : ℝ := ∫ μ in (0:ℝ)..1, f μ with hF1def
  have hF1 : F1 = 1 := hf.total
  set C0 : ℝ := ∫ μ in c..1, (μ - β * (1 - μ)) * f μ with hC0
  -- B(φ)
  have hB : HasDerivWithinAt
      (fun φ => β * (1 - φ) * δ + (Mc - ∫ μ in (0:ℝ)..tL c φ 1, μ * f μ) -
          β * φ * (Nc - ∫ μ in (0:ℝ)..tL c φ 1, (1 - μ) * f μ))
      (β * (-1) * δ + (-(c / (1 - c) * (0 * f 0))) -
        (β * 1 * (Nc - ∫ μ in (0:ℝ)..tL c 0 1, (1 - μ) * f μ) +
          β * 0 * (-(c / (1 - c) * ((1 - 0) * f 0))))) (Ici 0) 0 := by
    have t1 : HasDerivWithinAt (fun φ : ℝ => β * (1 - φ) * δ) (β * (-1) * δ) (Ici 0) 0 := by
      have := (((hasDerivWithinAt_id (0:ℝ) (Ici 0)).const_sub 1).const_mul β).mul_const δ
      simpa using this
    have t2 := hMt.const_sub Mc
    have t3 := ((hasDerivWithinAt_id (0:ℝ) (Ici 0)).const_mul β).mul (hNt.const_sub Nc)
    exact (t1.add t2).sub t3
  have hGd : HasDerivWithinAt (fun φ => cdf f 1 - cdf f (tL c φ 1))
      (-(c / (1 - c) * f 0)) (Ici 0) 0 := hFt.const_sub (cdf f 1)
  have hcdf0 : cdf f 0 = 0 := by simp [cdf]
  have hcdf1 : cdf f 1 = 1 := hf.total
  have G0 : cdf f 1 - cdf f (tL c 0 1) = 1 := by rw [hT0, hcdf0, hcdf1]; ring
  have hAd := (hasDerivWithinAt_const (0:ℝ) (Ici 0) κ).div hGd (by rw [G0]; exact one_ne_zero)
  have hfin := (hAd.mul hB).const_add C0
  have hlt1 : ∀ᶠ φ in 𝓝[Ici 0] (0:ℝ), φ < 1 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)
  have hevG : ∀ᶠ φ in 𝓝[Ici 0] (0:ℝ), κ < cdf f 1 - cdf f (tL c φ 1) :=
    hGd.continuousWithinAt.eventually
      (lt_mem_nhds (show κ < cdf f 1 - cdf f (tL c 0 1) by rw [G0]; exact hκ1))
  have hS : ∀ φ : ℝ, 0 ≤ φ → φ < 1 → κ < cdf f 1 - cdf f (tL c φ 1) →
      S f c β κ φ 1 = C0 + κ / (cdf f 1 - cdf f (tL c φ 1)) *
        (β * (1 - φ) * δ + (Mc - ∫ μ in (0:ℝ)..tL c φ 1, μ * f μ) -
          β * φ * (Nc - ∫ μ in (0:ℝ)..tL c φ 1, (1 - μ) * f μ)) := by
    intro φ h0 h1 h2
    exact S_phi f hf c β κ φ hc0 hc1 hβ0 hβ1 hκ0 hκ1 h0 h1 h2
  have hN1 : ∫ μ in (0:ℝ)..1, (1 - μ) * f μ = Nc + δ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (wN f hf 0 c ⟨le_rfl, zero_le_one⟩ ⟨hc0.le, hc1.le⟩)
      (wN f hf c 1 ⟨hc0.le, hc1.le⟩ ⟨zero_le_one, le_rfl⟩)).symm
  refine (hfin.congr_of_eventuallyEq ?_ ?_).congr_deriv ?_
  · filter_upwards [hlt1, hevG, self_mem_nhdsWithin] with φ h1 h2 h3 using
      hS φ h3 h1 h2
  · exact hS 0 le_rfl one_pos (by rw [G0]; exact hκ1)
  · simp only [Pi.div_apply]
    rw [hN1, G0, hT0]
    simp only [intervalIntegral.integral_same, sub_zero, zero_mul, mul_zero, mul_one, neg_zero,
      zero_sub, add_zero, mul_neg, sub_self, one_pow, div_one, zero_add, mul_one]
    ring


lemma dS_dsigma_aux (f : ℝ → ℝ) (c β κ : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hf : IsPriorDensity f) (hf1 : ContinuousWithinAt f (Set.Icc 0 1) 1) :
    HasDerivWithinAt (fun σ => S f c β κ 0 σ)
      (-κ * f 1 * ((1 - c) / c) * β * (∫ μ in c..1, (1 - μ) * f μ) +
        κ * (∫ μ in (0:ℝ)..1, μ * f μ) -
        κ * f 1 * ((1 - c) / c) * (∫ μ in (0:ℝ)..c, μ * f μ))
      (Set.Iic 1) 1 := by
  have h1c : 0 < 1 - c := by linarith
  have hi := hf.integrable
  have iM : IntervalIntegrable (fun μ => μ * f μ) volume 0 1 :=
    wM f hf 0 1 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  have iN : IntervalIntegrable (fun μ => (1 - μ) * f μ) volume 0 1 :=
    wN f hf 0 1 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  have hF1' : HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, f x) (f 1) (Iic 1) 1 := ftc1 f hi hf1
  have hM1' : HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, x * f x) (1 * f 1) (Iic 1) 1 :=
    ftc1 (fun x => x * f x) iM (continuousWithinAt_id.mul hf1)
  have hN1' : HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, (1 - x) * f x) ((1 - 1) * f 1)
      (Iic 1) 1 :=
    ftc1 (fun x => (1 - x) * f x) iN ((continuousWithinAt_const.sub continuousWithinAt_id).mul hf1)
  -- the threshold t_H(σ)
  have hT : HasDerivWithinAt (fun σ => tH c 0 σ) ((1 - c) / c) (Iic 1) 1 := by
    have hH : (fun σ : ℝ => tH c 0 σ) = fun σ => c / (1 - (1 - c) * σ) := by
      funext σ; exact tH_zero_eq c σ
    have h1 : HasDerivAt (fun σ : ℝ => 1 - (1 - c) * σ) (-(1 - c)) 1 := by
      have := ((hasDerivAt_id (1:ℝ)).const_mul (1 - c)).const_sub 1
      simpa using this
    have := (hasDerivAt_const (1:ℝ) c).div h1 (by simp; exact hc0.ne')
    have h2 : HasDerivAt (fun σ : ℝ => c / (1 - (1 - c) * σ)) ((1 - c) / c) 1 := by
      refine HasDerivAt.congr_deriv this ?_
      have e : 1 - (1 - c) * 1 = c := by ring
      rw [e]
      have hc : c ≠ 0 := hc0.ne'
      field_simp
      ring
    rw [hH]
    exact h2.hasDerivWithinAt
  have hT1 : tH c 0 1 = 1 := tH_one c 0 hc0 zero_lt_one
  have hmaps : MapsTo (fun σ => tH c 0 σ) (Iic 1) (Iic 1) :=
    fun σ hσ => tH_zero_le c σ hc0 hc1 hσ
  have hF1'' : HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, f x) (f 1) (Iic 1)
      ((fun σ => tH c 0 σ) 1) := by simpa only [hT1] using hF1'
  have hM1'' : HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, x * f x) (1 * f 1) (Iic 1)
      ((fun σ => tH c 0 σ) 1) := by simpa only [hT1] using hM1'
  have hN1'' : HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, (1 - x) * f x) ((1 - 1) * f 1) (Iic 1)
      ((fun σ => tH c 0 σ) 1) := by simpa only [hT1] using hN1'
  have hFt := hF1''.scomp (1:ℝ) hT hmaps
  have hMt := hM1''.scomp (1:ℝ) hT hmaps
  have hNt := hN1''.scomp (1:ℝ) hT hmaps
  simp only [smul_eq_mul] at hFt hMt hNt
  -- constants
  set δ : ℝ := ∫ μ in c..1, (1 - μ) * f μ with hδ
  set Mc : ℝ := ∫ μ in (0:ℝ)..c, μ * f μ with hMc
  set Nc : ℝ := ∫ μ in (0:ℝ)..c, (1 - μ) * f μ with hNc
  set C0 : ℝ := ∫ μ in c..1, (μ - β * (1 - μ)) * f μ with hC0
  have hB : HasDerivWithinAt
      (fun σ => β * ((∫ μ in (0:ℝ)..tH c 0 σ, (1 - μ) * f μ) - Nc) -
          (1 - σ) * ((∫ μ in (0:ℝ)..tH c 0 σ, μ * f μ) - Mc) + σ * Mc)
      (β * ((1 - c) / c * ((1 - 1) * f 1)) -
        ((-1) * ((∫ μ in (0:ℝ)..tH c 0 1, μ * f μ) - Mc) +
          (1 - 1) * ((1 - c) / c * (1 * f 1))) + 1 * Mc) (Iic 1) 1 := by
    have t1 := (hNt.sub_const Nc).const_mul β
    have t2 := ((hasDerivWithinAt_id (1:ℝ) (Iic 1)).const_sub 1).mul (hMt.sub_const Mc)
    have t3 := (hasDerivWithinAt_id (1:ℝ) (Iic 1)).mul_const Mc
    have := (t1.sub t2).add t3
    exact this
  have hGd : HasDerivWithinAt (fun σ => cdf f (tH c 0 σ) - cdf f 0)
      ((1 - c) / c * f 1) (Iic 1) 1 := hFt.sub_const (cdf f 0)
  have hcdf0 : cdf f 0 = 0 := by simp [cdf]
  have hcdf1 : cdf f 1 = 1 := hf.total
  have G0 : cdf f (tH c 0 1) - cdf f 0 = 1 := by rw [hT1, hcdf0, hcdf1]; ring
  have hAd := (hasDerivWithinAt_const (1:ℝ) (Iic 1) κ).div hGd (by rw [G0]; exact one_ne_zero)
  have hfin := (hAd.mul hB).const_add C0
  have hpos : ∀ᶠ σ in 𝓝[Iic 1] (1:ℝ), 0 < σ :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one)
  have hevG : ∀ᶠ σ in 𝓝[Iic 1] (1:ℝ), κ < cdf f (tH c 0 σ) - cdf f 0 :=
    hGd.continuousWithinAt.eventually
      (lt_mem_nhds (show κ < cdf f (tH c 0 1) - cdf f 0 by rw [G0]; exact hκ1))
  have hS : ∀ σ : ℝ, 0 < σ → σ ≤ 1 → κ < cdf f (tH c 0 σ) - cdf f 0 →
      S f c β κ 0 σ = C0 + κ / (cdf f (tH c 0 σ) - cdf f 0) *
        (β * ((∫ μ in (0:ℝ)..tH c 0 σ, (1 - μ) * f μ) - Nc) -
          (1 - σ) * ((∫ μ in (0:ℝ)..tH c 0 σ, μ * f μ) - Mc) + σ * Mc) := by
    intro σ h0 h1 h2
    exact S_sigma f hf c β κ σ hc0 hc1 hβ0 hβ1 hκ0 hκ1 h0 h1 h2
  have hN1 : ∫ μ in (0:ℝ)..1, (1 - μ) * f μ = Nc + δ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (wN f hf 0 c ⟨le_rfl, zero_le_one⟩ ⟨hc0.le, hc1.le⟩)
      (wN f hf c 1 ⟨hc0.le, hc1.le⟩ ⟨zero_le_one, le_rfl⟩)).symm
  refine (hfin.congr_of_eventuallyEq ?_ ?_).congr_deriv ?_
  · filter_upwards [hpos, hevG, self_mem_nhdsWithin] with σ h1 h2 h3 using
      hS σ h1 h3 h2
  · exact hS 1 one_pos le_rfl (by rw [G0]; exact hκ1)
  · simp only [Pi.div_apply]
    rw [G0, hT1, hN1]
    simp only [sub_self, zero_mul, mul_zero, one_mul, zero_sub, mul_one, add_zero, zero_add,
      neg_mul, sub_zero, one_pow, div_one, mul_neg]
    ring

/-- A weighted integral of a nonnegative function is positive when the weight is positive
in the interior and the unweighted integral is positive. -/
lemma wpos (f w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hw : Continuous w) (hf0 : ∀ x ∈ Ioo a b, 0 ≤ f x) (hw0 : ∀ x ∈ Ioo a b, 0 < w x)
    (hint : 0 < ∫ x in a..b, f x) : 0 < ∫ x in a..b, w x * f x := by
  have hfi : IntegrableOn f (Ioo a b) volume := by
    have := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).1 hf
    exact this
  have hwfi : IntegrableOn (fun x => w x * f x) (Ioo a b) volume := by
    have h1 : IntegrableOn f (Icc a b) volume := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hf
      exact hf
    have : IntegrableOn (fun x => w x * f x) (Icc a b) volume :=
      h1.continuousOn_mul hw.continuousOn isCompact_Icc
    exact this.mono_set Ioo_subset_Icc_self
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] at hint ⊢
  have hnn : 0 ≤ ∫ x in Ioo a b, w x * f x :=
    setIntegral_nonneg measurableSet_Ioo (fun x hx => (mul_nonneg (hw0 x hx).le (hf0 x hx)))
  rcases hnn.lt_or_eq with h | h
  · exact h
  exfalso
  have hae : (fun x => w x * f x) =ᵐ[volume.restrict (Ioo a b)] 0 := by
    have := (integral_eq_zero_iff_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall
        (fun x hx => (mul_nonneg (hw0 x hx).le (hf0 x hx)))) ) hwfi).1 h.symm
    exact this
  have hf_ae : f =ᵐ[volume.restrict (Ioo a b)] 0 := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with x hx hxm
    have := (hw0 x hxm).ne'
    simpa [this] using hx
  have : ∫ x in Ioo a b, f x = 0 := integral_eq_zero_of_ae hf_ae
  linarith

lemma dgp (f : ℝ → ℝ) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hf : IsPriorDensity f) (hFc0 : 0 < cdf f c) (hFc1 : cdf f c < 1) :
    0 < deltaC f c ∧ 0 < gammaC f c := by
  have hi := hf.integrable
  have hi0c : IntervalIntegrable f volume 0 c :=
    hi.mono_set (by rw [uIcc_of_le zero_le_one, uIcc_of_le hc0.le]; exact Icc_subset_Icc le_rfl hc1.le)
  have hic1 : IntervalIntegrable f volume c 1 :=
    hi.mono_set (by rw [uIcc_of_le zero_le_one, uIcc_of_le hc1.le]; exact Icc_subset_Icc hc0.le le_rfl)
  have hsum := intervalIntegral.integral_add_adjacent_intervals hi0c hic1
  rw [hf.total] at hsum
  have hnn : ∀ x ∈ Ioo (0:ℝ) 1, 0 ≤ f x := fun x hx => hf.nonneg x (Ioo_subset_Icc_self hx)
  constructor
  · apply wpos f (fun x => 1 - x) c 1 hc1.le hic1 (by fun_prop)
    · intro x hx; exact hnn x ⟨hc0.trans hx.1, hx.2⟩
    · intro x hx; linarith [hx.2]
    · have : cdf f c = ∫ t in (0:ℝ)..c, f t := rfl
      linarith
  · apply wpos f (fun x => x) 0 c hc0.le hi0c (by fun_prop)
    · intro x hx; exact hnn x ⟨hx.1, hx.2.trans hc1⟩
    · intro x hx; exact hx.1
    · exact hFc0


lemma exists_gt_right (g : ℝ → ℝ) (D : ℝ) (hD : 0 < D) (hg : HasDerivWithinAt g D (Ici 0) 0) :
    ∃ φ : ℝ, 0 < φ ∧ φ < 1 ∧ g 0 < g φ := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left] at hg
  have h1 := hg.eventually (lt_mem_nhds hD)
  have h2 : ∀ᶠ φ in 𝓝[>] (0:ℝ), φ < 1 := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)
  have h3 : ∀ᶠ φ in 𝓝[>] (0:ℝ), 0 < φ := self_mem_nhdsWithin
  obtain ⟨φ, a, b, c⟩ := (h1.and (h2.and h3)).exists
  refine ⟨φ, c, b, ?_⟩
  have h : 0 < slope g 0 φ := a
  rw [slope_def_field] at h
  have h4 : 0 < φ - 0 := by linarith
  have := (div_pos_iff_of_pos_right h4).1 h
  linarith

lemma exists_gt_left (g : ℝ → ℝ) (D : ℝ) (hD : D < 0) (hg : HasDerivWithinAt g D (Iic 1) 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ g 1 < g σ := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Iic_sdiff_right] at hg
  have h1 := hg.eventually (gt_mem_nhds hD)
  have h2 : ∀ᶠ σ in 𝓝[<] (1:ℝ), 0 < σ := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos)
  have h3 : ∀ᶠ σ in 𝓝[<] (1:ℝ), σ < 1 := self_mem_nhdsWithin
  obtain ⟨σ, a, b, c⟩ := (h1.and (h2.and h3)).exists
  refine ⟨σ, b, c, ?_⟩
  have h : slope g 1 σ < 0 := a
  rw [slope_def_field] at h
  have h4 : σ - 1 < 0 := by linarith
  by_contra hcon
  push_neg at hcon
  have : 0 ≤ (g σ - g 1) / (σ - 1) := div_nonneg_of_nonpos (by linarith) h4.le
  linarith

lemma mean_eq (f : ℝ → ℝ) (hf : IsPriorDensity f) :
    ∫ μ in (0:ℝ)..1, (1 - μ) * f μ = 1 - meanPrior f := by
  have h : (fun μ => (1 - μ) * f μ) = fun μ => f μ - μ * f μ := by funext μ; ring
  rw [h, intervalIntegral.integral_sub hf.integrable (wM f hf 0 1 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩), hf.total]
  rfl

lemma prop_i (f : ℝ → ℝ) (c β κ : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hf : IsPriorDensity f)
    (hf0 : ContinuousWithinAt f (Set.Icc 0 1) 0)
    (hFc0 : 0 < cdf f c) (hFc1 : cdf f c < 1)
    (h : β * (1 - meanPrior f) / (β * deltaC f c + gammaC f c) * ((1 - c) / c) < f 0) :
    ∃ φ : ℝ, 0 < φ ∧ φ < 1 ∧ S f c β κ 0 1 < S f c β κ φ 1 := by
  obtain ⟨hδ, hγ⟩ := dgp f c hc0 hc1 hf hFc0 hFc1
  have hY : 0 < β * deltaC f c + gammaC f c := by
    have := mul_nonneg hβ0 hδ.le
    linarith
  have hd := dS_dphi_aux f c β κ hc0 hc1 hβ0 hβ1 hκ0 hκ1 hf hf0
  have h1c : 0 < 1 - c := by linarith
  rw [mean_eq f hf] at hd
  have key : β * (1 - meanPrior f) * ((1 - c) / c) < f 0 * (β * deltaC f c + gammaC f c) := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hY] at h
    exact h
  have hD : 0 < -κ * β * (1 - meanPrior f) +
      c / (1 - c) * κ * f 0 * (β * (∫ μ in c..1, (1 - μ) * f μ) + ∫ μ in (0:ℝ)..c, μ * f μ) := by
    have e : -κ * β * (1 - meanPrior f) +
      c / (1 - c) * κ * f 0 * (β * (∫ μ in c..1, (1 - μ) * f μ) + ∫ μ in (0:ℝ)..c, μ * f μ) =
        κ * (c / (1 - c)) * (f 0 * (β * deltaC f c + gammaC f c) -
          β * (1 - meanPrior f) * ((1 - c) / c)) := by
      unfold deltaC gammaC
      field_simp
      ring
    rw [e]
    have : 0 < f 0 * (β * deltaC f c + gammaC f c) - β * (1 - meanPrior f) * ((1 - c) / c) := by
      linarith
    positivity
  exact exists_gt_right _ _ hD hd

lemma prop_ii (f : ℝ → ℝ) (c β κ : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hf : IsPriorDensity f)
    (hf1 : ContinuousWithinAt f (Set.Icc 0 1) 1)
    (hFc0 : 0 < cdf f c) (hFc1 : cdf f c < 1)
    (h : c / (1 - c) * (meanPrior f / (β * deltaC f c + gammaC f c)) < f 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ S f c β κ 0 1 < S f c β κ 0 σ := by
  obtain ⟨hδ, hγ⟩ := dgp f c hc0 hc1 hf hFc0 hFc1
  have hY : 0 < β * deltaC f c + gammaC f c := by
    have := mul_nonneg hβ0 hδ.le
    linarith
  have hd := dS_dsigma_aux f c β κ hc0 hc1 hβ0 hβ1 hκ0 hκ1 hf hf1
  have h1c : 0 < 1 - c := by linarith
  have key : c * meanPrior f < f 1 * ((1 - c) * (β * deltaC f c + gammaC f c)) := by
    have e : c / (1 - c) * (meanPrior f / (β * deltaC f c + gammaC f c)) =
        c * meanPrior f / ((1 - c) * (β * deltaC f c + gammaC f c)) := by
      field_simp
    rw [e, div_lt_iff₀ (mul_pos h1c hY)] at h
    exact h
  have hD : -κ * f 1 * ((1 - c) / c) * β * (∫ μ in c..1, (1 - μ) * f μ) +
        κ * (∫ μ in (0:ℝ)..1, μ * f μ) -
        κ * f 1 * ((1 - c) / c) * (∫ μ in (0:ℝ)..c, μ * f μ) < 0 := by
    have e : -κ * f 1 * ((1 - c) / c) * β * (∫ μ in c..1, (1 - μ) * f μ) +
        κ * (∫ μ in (0:ℝ)..1, μ * f μ) -
        κ * f 1 * ((1 - c) / c) * (∫ μ in (0:ℝ)..c, μ * f μ) =
        κ / c * (c * meanPrior f - f 1 * ((1 - c) * (β * deltaC f c + gammaC f c))) := by
      unfold deltaC gammaC meanPrior
      field_simp
      ring
    rw [e]
    have : c * meanPrior f - f 1 * ((1 - c) * (β * deltaC f c + gammaC f c)) < 0 := by linarith
    exact mul_neg_of_pos_of_neg (by positivity) this
  exact exists_gt_left _ _ hD hd

theorem solution (f : ℝ → ℝ) (c β κ : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hf : IsPriorDensity f)
    (hf0 : ContinuousWithinAt f (Set.Icc 0 1) 0)
    (hFc0 : 0 < cdf f c) (hFc1 : cdf f c < 1)
    (h : β * (1 - meanPrior f) / (β * deltaC f c + gammaC f c) * ((1 - c) / c) < f 0) :
    ∃ φ : ℝ, 0 < φ ∧ φ < 1 ∧ S f c β κ 0 1 < S f c β κ φ 1 :=
  prop_i f c β κ hc0 hc1 hβ0 hβ1 hκ0 hκ1 hf hf0 hFc0 hFc1 h
