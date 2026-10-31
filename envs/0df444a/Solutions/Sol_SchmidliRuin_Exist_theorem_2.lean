-- Prove2me | solution 1 for SchmidliRuin.Exist.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T16:21:34.133987+00:00
-- url     : https://prove2.me/submissions/f2beb6c8-d890-4544-87a1-d2fd7638d0a4

import Mathlib
import Definitions.Def_SchmidliRuin_Exist_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace SchmidliRuinWork

open SchmidliRuin.Verif

/-- `yfun u = K * ∫_0^u den⁻¹ + c/λ`; a solution of (5) is `g = 1 / yfun` on `[0, ∞)`. -/
noncomputable def yfun (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (g : ℝ → ℝ)
    (u : ℝ) : ℝ :=
  mu ^ 2 / (2 * sigma ^ 2) * (∫ x in (0 : ℝ)..u, (den c lam cb ν g x)⁻¹) + c / lam

lemma yfun_zero (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (g : ℝ → ℝ) :
    yfun c lam mu sigma cb ν g 0 = c / lam := by
  simp [yfun]

lemma g_eq_inv_yfun {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0)) {u : ℝ} (hu : 0 ≤ u) :
    g u = 1 / yfun c lam mu sigma cb ν g u :=
  (hs u hu).2.2.2

lemma yfun_continuousOn {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0)) {U : ℝ} (hU : 0 ≤ U) :
    ContinuousOn (yfun c lam mu sigma cb ν g) (Icc 0 U) := by
  have h1 := (hs U hU).2.2.1
  have h2 : ContinuousOn (fun u => ∫ x in (0 : ℝ)..u, (den c lam cb ν g x)⁻¹) (uIcc 0 U) :=
    intervalIntegral.continuousOn_primitive_interval' h1 left_mem_uIcc
  rw [uIcc_of_le hU] at h2
  exact (continuousOn_const.mul h2).add continuousOn_const

/-- Basic bounds for a strictly decreasing solution: `yfun ≥ c/λ`, `0 < g ≤ λ/c`. -/
lemma sol_bounds {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam)
    (hg : StrictAntiOn g (Ici 0)) (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0))
    {u : ℝ} (hu : 0 ≤ u) :
    c / lam ≤ yfun c lam mu sigma cb ν g u ∧ 0 < g u ∧ g u ≤ lam / c := by
  have hy0 := yfun_zero c lam mu sigma cb ν g
  have hcl : 0 < c / lam := div_pos hc hlam
  have hg0 : g 0 = lam / c := by
    rw [g_eq_inv_yfun hs le_rfl, hy0, one_div_div]
  have key : c / lam ≤ yfun c lam mu sigma cb ν g u := by
    by_contra hlt
    push Not at hlt
    rcases eq_or_lt_of_le hu with h0 | hpos
    · subst h0; rw [hy0] at hlt; exact lt_irrefl _ hlt
    have hgu0 : g u < g 0 := hg (self_mem_Ici) (mem_Ici.2 hu) hpos
    by_cases hyp : 0 < yfun c lam mu sigma cb ν g u
    · have : lam / c < g u := by
        rw [g_eq_inv_yfun hs hu, ← one_div_div c lam]
        exact one_div_lt_one_div_of_lt hyp hlt
      linarith
    · push Not at hyp
      have hcont := yfun_continuousOn hs hu
      have hmem : c / (2 * lam) ∈
          Icc (yfun c lam mu sigma cb ν g u) (yfun c lam mu sigma cb ν g 0) := by
        rw [hy0]
        have h2 : 0 < c / (2 * lam) := div_pos hc (by linarith)
        have h3 : c / (2 * lam) < c / lam := div_lt_div_of_pos_left hc hlam (by linarith)
        exact ⟨by linarith, h3.le⟩
      obtain ⟨t, ht, hyt⟩ := intermediate_value_Icc' hu hcont hmem
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [hy0] at hyt
        have : c / (2 * lam) < c / lam := div_lt_div_of_pos_left hc hlam (by linarith)
        linarith
      have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hgt0 : g t < g 0 := hg (self_mem_Ici) (mem_Ici.2 ht.1) htpos
      have : g t = 2 * lam / c := by
        rw [g_eq_inv_yfun hs ht.1, hyt, one_div_div]
      rw [this, hg0] at hgt0
      have : lam / c < 2 * lam / c := div_lt_div_of_pos_right (by linarith) hc
      linarith
  have hypos : 0 < yfun c lam mu sigma cb ν g u := lt_of_lt_of_le hcl key
  refine ⟨key, ?_, ?_⟩
  · rw [g_eq_inv_yfun hs hu]; exact one_div_pos.2 hypos
  · rw [g_eq_inv_yfun hs hu, ← one_div_div c lam]
    exact one_div_le_one_div_of_le hcl key

/-- A strictly decreasing solution is continuous on every `[0, U]`. -/
lemma sol_continuousOn {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam)
    (hg : StrictAntiOn g (Ici 0)) (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0))
    {U : ℝ} (hU : 0 ≤ U) : ContinuousOn g (Icc 0 U) := by
  have hcont := yfun_continuousOn hs hU
  have hne : ∀ x ∈ Icc (0 : ℝ) U, yfun c lam mu sigma cb ν g x ≠ 0 := fun x hx =>
    ne_of_gt (lt_of_lt_of_le (div_pos hc hlam) (sol_bounds hc hlam hg hs hx.1).1)
  exact (continuousOn_const.div hcont hne).congr (fun x hx => g_eq_inv_yfun hs hx.1)

/-- `yfun` is strictly increasing on `[0, ∞)` (it is `1 / g`). -/
lemma yfun_strictMonoOn {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam)
    (hg : StrictAntiOn g (Ici 0)) (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0)) :
    StrictMonoOn (yfun c lam mu sigma cb ν g) (Ici 0) := by
  intro a ha b hb hab
  have hya := sol_bounds hc hlam hg hs (mem_Ici.1 ha)
  have hyb := sol_bounds hc hlam hg hs (mem_Ici.1 hb)
  have hgab : g b < g a := hg ha hb hab
  have hpa : 0 < yfun c lam mu sigma cb ν g a := lt_of_lt_of_le (div_pos hc hlam) hya.1
  have hpb : 0 < yfun c lam mu sigma cb ν g b := lt_of_lt_of_le (div_pos hc hlam) hyb.1
  rw [g_eq_inv_yfun hs (mem_Ici.1 ha), g_eq_inv_yfun hs (mem_Ici.1 hb)] at hgab
  exact (one_div_lt_one_div hpb hpa).1 hgab

/-- The bracket of (5) at retention `b` (the function whose infimum over `b ∈ [0,1]` is `den`). -/
noncomputable def phi (c lam : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (g : ℝ → ℝ) (x b : ℝ) : ℝ :=
  lam * (tail ν x b + ∫ z in (0 : ℝ)..x, tail ν (x - z) b * g z) - (c - cb b) * g x

lemma den_eq_sInf_phi (c lam : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (g : ℝ → ℝ) (x : ℝ) :
    den c lam cb ν g x = sInf ((fun b => phi c lam cb ν g x b) '' Icc 0 1) := rfl

lemma cb_nonneg {c : ℝ} {cb : ℝ → ℝ} (hcb : ReinsPremium c cb) {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    0 ≤ cb b := by
  have h := hcb.1 hb ⟨zero_le_one, le_rfl⟩ hb.2
  rw [hcb.2.2.1] at h
  exact h

lemma tail_nonneg (ν : Measure ℝ) [IsProbabilityMeasure ν] (x b : ℝ) : 0 ≤ tail ν x b := by
  unfold tail
  split_ifs
  · exact le_rfl
  · linarith [cdf_le_one ν (x / b)]

lemma tail_le_one (ν : Measure ℝ) (x b : ℝ) : tail ν x b ≤ 1 := by
  unfold tail
  split_ifs
  · exact zero_le_one
  · linarith [cdf_nonneg ν (x / b)]

/-- Every bracket is at least `-λ` when `0 ≤ g ≤ λ/c` on `[0, x]`. -/
lemma phi_ge {c lam : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν] {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hcb : ReinsPremium c cb) {x : ℝ} (hx : 0 ≤ x)
    (hg0 : ∀ z ∈ Icc (0 : ℝ) x, 0 ≤ g z) (hgx : g x ≤ lam / c) {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    -lam ≤ phi c lam cb ν g x b := by
  unfold phi
  have h1 : 0 ≤ tail ν x b := tail_nonneg ν x b
  have h2 : 0 ≤ ∫ z in (0 : ℝ)..x, tail ν (x - z) b * g z :=
    intervalIntegral.integral_nonneg hx (fun z hz => mul_nonneg (tail_nonneg ν _ _) (hg0 z hz))
  have h3 : 0 ≤ cb b := cb_nonneg hcb hb
  have hgx0 : 0 ≤ g x := hg0 x ⟨hx, le_rfl⟩
  have h4 : (c - cb b) * g x ≤ lam := by
    have : (c - cb b) * g x ≤ c * g x := by nlinarith
    have : c * g x ≤ c * (lam / c) := mul_le_mul_of_nonneg_left hgx hc.le
    have : c * (lam / c) = lam := by field_simp
    linarith
  nlinarith

lemma den_bddBelow {c lam : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν] {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hcb : ReinsPremium c cb) {x : ℝ} (hx : 0 ≤ x)
    (hg0 : ∀ z ∈ Icc (0 : ℝ) x, 0 ≤ g z) (hgx : g x ≤ lam / c) :
    BddBelow ((fun b => phi c lam cb ν g x b) '' Icc 0 1) := by
  refine ⟨-lam, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  exact phi_ge hc hlam hcb hx hg0 hgx hb

/-- `den ≤` each bracket, and `den ≥ -λ`. -/
lemma den_le_phi {c lam : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν] {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hcb : ReinsPremium c cb) {x : ℝ} (hx : 0 ≤ x)
    (hg0 : ∀ z ∈ Icc (0 : ℝ) x, 0 ≤ g z) (hgx : g x ≤ lam / c) {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    den c lam cb ν g x ≤ phi c lam cb ν g x b := by
  rw [den_eq_sInf_phi]
  exact csInf_le (den_bddBelow hc hlam hcb hx hg0 hgx) (mem_image_of_mem _ hb)

lemma den_ge {c lam : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν] {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hcb : ReinsPremium c cb) {x : ℝ} (hx : 0 ≤ x)
    (hg0 : ∀ z ∈ Icc (0 : ℝ) x, 0 ≤ g z) (hgx : g x ≤ lam / c) :
    -lam ≤ den c lam cb ν g x := by
  rw [den_eq_sInf_phi]
  refine le_csInf ((nonempty_Icc.2 zero_le_one).image _) ?_
  rintro _ ⟨b, hb, rfl⟩
  exact phi_ge hc hlam hcb hx hg0 hgx hb

/-- Increment formula: `yfun b - yfun a = K ∫_a^b den⁻¹` for `0 ≤ a, b`. -/
lemma yfun_sub {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    yfun c lam mu sigma cb ν g b - yfun c lam mu sigma cb ν g a =
      mu ^ 2 / (2 * sigma ^ 2) * ∫ x in a..b, (den c lam cb ν g x)⁻¹ := by
  have h := intervalIntegral.integral_interval_sub_left (hs b hb).2.2.1 (hs a ha).2.2.1
  unfold yfun
  rw [← h]
  ring

/-- C2 from continuity: a strictly decreasing solution whose `den` is continuous on `(0,∞)` has
`den > 0` there (condition (6)). -/
lemma den_pos_of_continuousOn {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hg : StrictAntiOn g (Ici 0)) (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0))
    (hcont : ContinuousOn (den c lam cb ν g) (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    0 < den c lam cb ν g x := by
  have hne : den c lam cb ν g x ≠ 0 := (hs (x + 1) (mem_Ici.2 (by linarith))).2.1 x ⟨hx, by linarith⟩
  by_contra hle
  push Not at hle
  have hneg : den c lam cb ν g x < 0 := lt_of_le_of_ne hle hne
  have hca : ContinuousAt (den c lam cb ν g) x := hcont.continuousAt (Ioi_mem_nhds hx)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hca.eventually (gt_mem_nhds hneg))
  set b := x + ε / 2 with hbdef
  have hxb : x < b := by linarith
  have hint : IntervalIntegrable (fun t => (den c lam cb ν g t)⁻¹) volume x b := by
    refine ((hs b (mem_Ici.2 (by linarith))).2.2.1).mono_set ?_
    rw [uIcc_of_le hxb.le, uIcc_of_le (by linarith : (0 : ℝ) ≤ b)]
    exact Icc_subset_Icc hx.le le_rfl
  have hpos : 0 < ∫ t in x..b, -(den c lam cb ν g t)⁻¹ := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hint.neg ?_ hxb
    intro t ht
    have hd : dist t x < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
    have := hball hd
    simp only [Left.neg_pos_iff, inv_lt_zero]
    exact this
  rw [intervalIntegral.integral_neg] at hpos
  have hK : 0 < mu ^ 2 / (2 * sigma ^ 2) := by positivity
  have hsub := yfun_sub hs hx.le (by linarith : (0 : ℝ) ≤ b)
  have hmono := yfun_strictMonoOn hc hlam hg hs (mem_Ici.2 hx.le) (mem_Ici.2 (by linarith)) hxb
  have : mu ^ 2 / (2 * sigma ^ 2) * ∫ t in x..b, (den c lam cb ν g t)⁻¹ < 0 :=
    mul_neg_of_pos_of_neg hK (by linarith)
  linarith

/-! ### C1: continuity of the denominator -/

lemma tail_antitone (ν : Measure ℝ) {b : ℝ} (hb : 0 ≤ b) : Antitone (fun x => tail ν x b) := by
  intro x y hxy
  simp only [tail]
  split_ifs with h
  · exact le_rfl
  · have : x / b ≤ y / b := div_le_div_of_nonneg_right hxy hb
    linarith [monotone_cdf ν this]

/-- The convolution term of the bracket. -/
noncomputable def conv (ν : Measure ℝ) (g : ℝ → ℝ) (x b : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..x, tail ν (x - z) b * g z

lemma tail_sub_intervalIntegrable (ν : Measure ℝ) {b : ℝ} (hb : 0 ≤ b) (x u v : ℝ) :
    IntervalIntegrable (fun z => tail ν (x - z) b) volume u v := by
  have : Monotone (fun z => tail ν (x - z) b) := fun z w hzw =>
    tail_antitone ν hb (by linarith)
  exact this.intervalIntegrable

lemma tail_intervalIntegrable (ν : Measure ℝ) {b : ℝ} (hb : 0 ≤ b) (u v : ℝ) :
    IntervalIntegrable (fun z => tail ν z b) volume u v :=
  (tail_antitone ν hb).intervalIntegrable

/-- The convolution term is `M`-Lipschitz in `x` (uniformly in `b`) when `0 ≤ g ≤ M`. -/
lemma conv_sub_le {ν : Measure ℝ} [IsProbabilityMeasure ν] {g : ℝ → ℝ} {M : ℝ}
    {b : ℝ} (hb : 0 ≤ b) {x0 x : ℝ} (hx0 : 0 ≤ x0) (hx : x0 ≤ x)
    (hgc : ContinuousOn g (Icc 0 x)) (hg0 : ∀ z ∈ Icc (0:ℝ) x, 0 ≤ g z)
    (hgM : ∀ z ∈ Icc (0:ℝ) x, g z ≤ M) :
    |conv ν g x b - conv ν g x0 b| ≤ M * (x - x0) := by
  have hM : 0 ≤ M := le_trans (hg0 0 ⟨le_rfl, hx0.trans hx⟩) (hgM 0 ⟨le_rfl, hx0.trans hx⟩)
  have hcont : ∀ u v, u ∈ Icc (0:ℝ) x → v ∈ Icc (0:ℝ) x → ContinuousOn g (uIcc u v) := by
    intro u v hu hv
    exact hgc.mono (uIcc_subset_Icc hu hv)
  have hI : ∀ (y : ℝ) u v, u ∈ Icc (0:ℝ) x → v ∈ Icc (0:ℝ) x →
      IntervalIntegrable (fun z => tail ν (y - z) b * g z) volume u v := fun y u v hu hv =>
    (tail_sub_intervalIntegrable ν hb y u v).mul_continuousOn (hcont u v hu hv)
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) x := ⟨le_rfl, hx0.trans hx⟩
  have hx0m : x0 ∈ Icc (0:ℝ) x := ⟨hx0, hx⟩
  have hxm : x ∈ Icc (0:ℝ) x := ⟨hx0.trans hx, le_rfl⟩
  have hsplit : conv ν g x b = (∫ z in (0:ℝ)..x0, tail ν (x - z) b * g z)
      + ∫ z in x0..x, tail ν (x - z) b * g z := by
    unfold conv
    rw [intervalIntegral.integral_add_adjacent_intervals (hI x 0 x0 h0 hx0m) (hI x x0 x hx0m hxm)]
  have hB1 : 0 ≤ ∫ z in x0..x, tail ν (x - z) b * g z :=
    intervalIntegral.integral_nonneg hx
      (fun z hz => mul_nonneg (tail_nonneg ν _ _) (hg0 z ⟨hx0.trans hz.1, hz.2⟩))
  have hB2 : ∫ z in x0..x, tail ν (x - z) b * g z ≤ M * (x - x0) := by
    have hmono := intervalIntegral.integral_mono_on hx (hI x x0 x hx0m hxm)
      (intervalIntegrable_const (c := M)) (fun z hz => by
        have h1 := tail_le_one ν (x - z) b
        have h2 := tail_nonneg ν (x - z) b
        have h3 := hg0 z ⟨hx0.trans hz.1, hz.2⟩
        have h4 := hgM z ⟨hx0.trans hz.1, hz.2⟩
        nlinarith)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    linarith [mul_comm M (x - x0)]
  set D := (∫ z in (0:ℝ)..x0, tail ν (x - z) b * g z)
    - ∫ z in (0:ℝ)..x0, tail ν (x0 - z) b * g z with hD
  have hDle : D ≤ 0 := by
    have hle : ∫ z in (0:ℝ)..x0, tail ν (x - z) b * g z ≤
        ∫ z in (0:ℝ)..x0, tail ν (x0 - z) b * g z :=
      intervalIntegral.integral_mono_on hx0 (hI x 0 x0 h0 hx0m) (hI x0 0 x0 h0 hx0m) (fun z hz =>
        mul_le_mul_of_nonneg_right (tail_antitone ν hb (by linarith)) (hg0 z ⟨hz.1, hz.2.trans hx⟩))
    linarith
  have hDge : -(M * (x - x0)) ≤ D := by
    have e1 : D = ∫ z in (0:ℝ)..x0, (tail ν (x - z) b - tail ν (x0 - z) b) * g z := by
      rw [hD, ← intervalIntegral.integral_sub (hI x 0 x0 h0 hx0m) (hI x0 0 x0 h0 hx0m)]
      congr 1; ext z; ring
    have e2 : ∫ z in (0:ℝ)..x0, (tail ν (x - z) b - tail ν (x0 - z) b) * M ≤
        ∫ z in (0:ℝ)..x0, (tail ν (x - z) b - tail ν (x0 - z) b) * g z := by
      refine intervalIntegral.integral_mono_on hx0 ?_ ?_ (fun z hz => ?_)
      · exact ((tail_sub_intervalIntegrable ν hb x 0 x0).sub
          (tail_sub_intervalIntegrable ν hb x0 0 x0)).mul_const M
      · exact ((tail_sub_intervalIntegrable ν hb x 0 x0).sub
          (tail_sub_intervalIntegrable ν hb x0 0 x0)).mul_continuousOn (hcont 0 x0 h0 hx0m)
      · have hneg : tail ν (x - z) b - tail ν (x0 - z) b ≤ 0 := by
          linarith [tail_antitone ν hb (show x0 - z ≤ x - z by linarith)]
        exact mul_le_mul_of_nonpos_left (hgM z ⟨hz.1, hz.2.trans hx⟩) hneg
    have e3 : ∫ z in (0:ℝ)..x0, (tail ν (x - z) b - tail ν (x0 - z) b) * M =
        ((∫ z in (0:ℝ)..x0, tail ν (x - z) b) - ∫ z in (0:ℝ)..x0, tail ν (x0 - z) b) * M := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub
        (tail_sub_intervalIntegrable ν hb x 0 x0) (tail_sub_intervalIntegrable ν hb x0 0 x0)]
    have e4 : (∫ z in (0:ℝ)..x0, tail ν (x - z) b) - ∫ z in (0:ℝ)..x0, tail ν (x0 - z) b =
        (∫ z in x0..x, tail ν z b) - ∫ z in (0:ℝ)..(x - x0), tail ν z b := by
      rw [intervalIntegral.integral_comp_sub_left (fun z => tail ν z b) x,
        intervalIntegral.integral_comp_sub_left (fun z => tail ν z b) x0]
      simp only [sub_zero, sub_self]
      have a1 := intervalIntegral.integral_add_adjacent_intervals
        (tail_intervalIntegrable ν hb 0 (x - x0)) (tail_intervalIntegrable ν hb (x - x0) x)
      have a2 := intervalIntegral.integral_add_adjacent_intervals
        (tail_intervalIntegrable ν hb 0 x0) (tail_intervalIntegrable ν hb x0 x)
      linarith
    have e5 : 0 ≤ ∫ z in x0..x, tail ν z b :=
      intervalIntegral.integral_nonneg hx (fun z _ => tail_nonneg ν z b)
    have e6 : ∫ z in (0:ℝ)..(x - x0), tail ν z b ≤ x - x0 := by
      have hm := intervalIntegral.integral_mono_on (by linarith : (0:ℝ) ≤ x - x0)
        (tail_intervalIntegrable ν hb 0 (x - x0)) (intervalIntegrable_const (c := (1:ℝ)))
        (fun z _ => tail_le_one ν z b)
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at hm
      exact hm
    rw [e3, e4] at e2
    have hA : -(x - x0) ≤ (∫ z in x0..x, tail ν z b) - ∫ z in (0:ℝ)..(x - x0), tail ν z b := by
      linarith
    have hAM := mul_le_mul_of_nonneg_right hA hM
    rw [e1]
    linarith
  have hconv0 : conv ν g x0 b = ∫ z in (0:ℝ)..x0, tail ν (x0 - z) b * g z := rfl
  rw [abs_le, hsplit, hconv0]
  constructor <;> linarith

/-- `x ↦ tail ν x b` is continuous at `x0 > 0`, uniformly in `b ∈ [0,1]`. -/
lemma tail_uniform {ν : Measure ℝ} [IsProbabilityMeasure ν] (hcdf : Continuous (cdf ν))
    {x0 : ℝ} (hx0 : 0 < x0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x, |x - x0| < δ → ∀ b ∈ Icc (0:ℝ) 1, |tail ν x b - tail ν x0 b| < ε := by
  have hHc : Continuous (fun x : ℝ => cdf ν |x|) := hcdf.comp continuous_abs
  have hHt : Tendsto (fun x : ℝ => cdf ν |x|) (cocompact ℝ) (𝓝 1) := by
    rw [cocompact_eq_atBot_atTop]
    exact Tendsto.sup ((tendsto_cdf_atTop ν).comp tendsto_abs_atBot_atTop)
      ((tendsto_cdf_atTop ν).comp tendsto_abs_atTop_atTop)
  have hU := hHc.uniformContinuous_of_tendsto_cocompact hHt
  obtain ⟨δG, hδG, hG⟩ := Metric.uniformContinuous_iff.1 hU ε hε
  obtain ⟨T0, hT0⟩ := eventually_atTop.1
    ((tendsto_order.1 (tendsto_cdf_atTop ν)).1 (1 - ε) (by linarith))
  set T1 := max T0 1 with hT1
  have hT1pos : 0 < T1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set β := x0 / (2 * T1) with hβ
  have hβpos : 0 < β := by positivity
  refine ⟨min (x0 / 2) (β * δG), lt_min (by linarith) (mul_pos hβpos hδG), ?_⟩
  intro x hx b hb
  have hx1 : |x - x0| < x0 / 2 := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : |x - x0| < β * δG := lt_of_lt_of_le hx (min_le_right _ _)
  have hxpos : x0 / 2 < x := by have := (abs_lt.1 hx1).1; linarith
  unfold tail
  split_ifs with h0
  · simpa using hε
  have hbpos : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm h0)
  by_cases hbβ : b < β
  · have key : ∀ y, x0 / 2 ≤ y → T0 ≤ y / b := by
      intro y hy
      have hT : T1 ≤ y / b := by
        rw [le_div_iff₀ hbpos]
        have h1 : T1 * b ≤ T1 * β := mul_le_mul_of_nonneg_left hbβ.le hT1pos.le
        have h2 : T1 * β = x0 / 2 := by rw [hβ]; field_simp
        linarith
      exact le_trans (le_max_left _ _) hT
    have g1 := hT0 _ (key x hxpos.le)
    have g2 := hT0 _ (key x0 (by linarith))
    have l1 := cdf_le_one ν (x / b)
    have l2 := cdf_le_one ν (x0 / b)
    rw [abs_lt]; constructor <;> linarith
  · push Not at hbβ
    have hxn : 0 ≤ x / b := div_nonneg (by linarith) hbpos.le
    have hx0n : 0 ≤ x0 / b := div_nonneg hx0.le hbpos.le
    have hd : dist (x / b) (x0 / b) < δG := by
      rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hbpos, div_lt_iff₀ hbpos]
      have hm : β * δG ≤ b * δG := mul_le_mul_of_nonneg_right hbβ hδG.le
      linarith
    have hGd := hG hd
    simp only [Real.dist_eq, abs_of_nonneg hxn, abs_of_nonneg hx0n] at hGd
    rw [show 1 - cdf ν (x / b) - (1 - cdf ν (x0 / b)) = -(cdf ν (x / b) - cdf ν (x0 / b)) by ring,
      abs_neg]
    exact hGd

/-- C1: `den g` is continuous on `(0, ∞)` for `g` continuous on `[0,∞)` with `0 ≤ g ≤ λ/c`. -/
lemma den_continuousOn_of {c lam : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {g : ℝ → ℝ} (hc : 0 < c) (hlam : 0 < lam) (hcb : ReinsPremium c cb)
    (hcdf : Continuous (cdf ν)) (hgc : ContinuousOn g (Ici 0))
    (hg0 : ∀ z, 0 ≤ z → 0 ≤ g z) (hgM : ∀ z, 0 ≤ z → g z ≤ lam / c) :
    ContinuousOn (den c lam cb ν g) (Ioi 0) := by
  rw [Metric.continuousOn_iff]
  intro x0 hx0 ε hε
  have hx0 : 0 < x0 := hx0
  set M := lam / c with hMdef
  have hMpos : 0 < M := div_pos hlam hc
  set Cc := c + cb 0 + 1 with hCc
  have hcb0 : 0 ≤ cb 0 := cb_nonneg hcb ⟨le_rfl, zero_le_one⟩
  have hCcpos : 0 < Cc := by linarith
  obtain ⟨δ1, hδ1, h1⟩ := tail_uniform hcdf hx0 (show 0 < ε / (6 * lam) by positivity)
  have hga : ContinuousAt g x0 := hgc.continuousAt (Ici_mem_nhds hx0)
  obtain ⟨δ3, hδ3, h3⟩ := Metric.continuousAt_iff.1 hga (ε / (6 * Cc)) (by positivity)
  set δ2 := ε / (6 * lam * M) with hδ2
  have hδ2pos : 0 < δ2 := by positivity
  refine ⟨min δ1 (min δ2 δ3), lt_min hδ1 (lt_min hδ2pos hδ3), ?_⟩
  intro x hx hdist
  have hx : 0 < x := hx
  rw [Real.dist_eq] at hdist ⊢
  have hd1 : |x - x0| < δ1 := lt_of_lt_of_le hdist (min_le_left _ _)
  have hd2 : |x - x0| < δ2 :=
    lt_of_lt_of_le hdist ((min_le_right _ _).trans (min_le_left _ _))
  have hd3 : dist x x0 < δ3 := by
    rw [Real.dist_eq]; exact lt_of_lt_of_le hdist ((min_le_right _ _).trans (min_le_right _ _))
  have hgx := h3 hd3
  rw [Real.dist_eq] at hgx
  have hconv : ∀ b ∈ Icc (0:ℝ) 1, |conv ν g x b - conv ν g x0 b| ≤ M * |x - x0| := by
    intro b hb
    rcases le_total x0 x with hle | hle
    · rw [abs_of_nonneg (by linarith : 0 ≤ x - x0)]
      exact conv_sub_le (ν := ν) (g := g) hb.1 hx0.le hle (hgc.mono Icc_subset_Ici_self)
        (fun z hz => hg0 z hz.1) (fun z hz => hgM z hz.1)
    · rw [abs_sub_comm, abs_sub_comm x x0, abs_of_nonneg (by linarith : 0 ≤ x0 - x)]
      exact conv_sub_le (ν := ν) (g := g) hb.1 hx.le hle (hgc.mono Icc_subset_Ici_self)
        (fun z hz => hg0 z hz.1) (fun z hz => hgM z hz.1)
  have hphi : ∀ b ∈ Icc (0:ℝ) 1,
      |phi c lam cb ν g x b - phi c lam cb ν g x0 b| ≤ ε / 2 := by
    intro b hb
    have ht := h1 x hd1 b hb
    have hcv := hconv b hb
    have hcbb : 0 ≤ cb b := cb_nonneg hcb hb
    have hcbb' : cb b ≤ cb 0 := hcb.1 ⟨le_rfl, zero_le_one⟩ hb hb.1
    have hcabs : |c - cb b| ≤ Cc := by rw [abs_le]; constructor <;> linarith
    have e : phi c lam cb ν g x b - phi c lam cb ν g x0 b =
        lam * (tail ν x b - tail ν x0 b) + lam * (conv ν g x b - conv ν g x0 b)
          - (c - cb b) * (g x - g x0) := by
      unfold phi conv; ring
    rw [e]
    have b1 : |lam * (tail ν x b - tail ν x0 b)| ≤ ε / 6 := by
      rw [abs_mul, abs_of_pos hlam]
      have k1 := mul_lt_mul_of_pos_left ht hlam
      have k2 : lam * (ε / (6 * lam)) = ε / 6 := by field_simp
      linarith
    have b2 : |lam * (conv ν g x b - conv ν g x0 b)| ≤ ε / 6 := by
      rw [abs_mul, abs_of_pos hlam]
      have k1 : M * |x - x0| ≤ M * δ2 := mul_le_mul_of_nonneg_left hd2.le hMpos.le
      have k2 : lam * (M * δ2) = ε / 6 := by rw [hδ2]; field_simp
      have k3 := mul_le_mul_of_nonneg_left (hcv.trans k1) hlam.le
      linarith
    have b3 : |(c - cb b) * (g x - g x0)| ≤ ε / 6 := by
      rw [abs_mul]
      have k1 := mul_le_mul hcabs hgx.le (abs_nonneg _) hCcpos.le
      have k2 : Cc * (ε / (6 * Cc)) = ε / 6 := by field_simp
      linarith
    calc _ ≤ |lam * (tail ν x b - tail ν x0 b) + lam * (conv ν g x b - conv ν g x0 b)|
          + |(c - cb b) * (g x - g x0)| := abs_sub _ _
      _ ≤ |lam * (tail ν x b - tail ν x0 b)| + |lam * (conv ν g x b - conv ν g x0 b)|
          + |(c - cb b) * (g x - g x0)| := by gcongr; exact abs_add_le _ _
      _ ≤ ε / 2 := by linarith
  have hgx0' : ∀ z ∈ Icc (0:ℝ) x, 0 ≤ g z := fun z hz => hg0 z hz.1
  have hgx0'' : ∀ z ∈ Icc (0:ℝ) x0, 0 ≤ g z := fun z hz => hg0 z hz.1
  have up : den c lam cb ν g x - ε / 2 ≤ den c lam cb ν g x0 := by
    rw [den_eq_sInf_phi c lam cb ν g x0]
    refine le_csInf ((nonempty_Icc.2 zero_le_one).image _) ?_
    rintro _ ⟨b, hb, rfl⟩
    have k1 := den_le_phi (ν := ν) (g := g) (cb := cb) hc hlam hcb hx.le hgx0' (hgM x hx.le) hb
    have k2 := (abs_le.1 (hphi b hb)).2
    linarith
  have dn : den c lam cb ν g x0 - ε / 2 ≤ den c lam cb ν g x := by
    rw [den_eq_sInf_phi c lam cb ν g x]
    refine le_csInf ((nonempty_Icc.2 zero_le_one).image _) ?_
    rintro _ ⟨b, hb, rfl⟩
    have k1 := den_le_phi (ν := ν) (g := g) (cb := cb) hc hlam hcb hx0.le hgx0'' (hgM x0 hx0.le) hb
    have k2 := (abs_le.1 (hphi b hb)).1
    linarith
  rw [abs_lt]; constructor <;> linarith


/-! ### C2: positivity of the denominator along a solution -/

lemma sol_continuousOn_Ici {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam)
    (hg : StrictAntiOn g (Ici 0)) (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0)) :
    ContinuousOn g (Ici 0) := by
  intro x hx
  have hx' : (0:ℝ) ≤ x := hx
  have h := sol_continuousOn hc hlam hg hs (U := x + 1) (by linarith)
  have hxm : x ∈ Icc (0:ℝ) (x + 1) := ⟨hx', by linarith⟩
  refine (h x hxm).mono_of_mem_nhdsWithin ?_
  rw [← Ici_inter_Iic]
  exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))

lemma den_continuousOn_sol {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hcb : ReinsPremium c cb) (hν : ClaimLaw ν)
    (hg : StrictAntiOn g (Ici 0)) (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0)) :
    ContinuousOn (den c lam cb ν g) (Ioi 0) := by
  have := hν.1
  exact den_continuousOn_of hc hlam hcb hν.2.2 (sol_continuousOn_Ici hc hlam hg hs)
    (fun z hz => (sol_bounds hc hlam hg hs hz).2.1.le) (fun z hz => (sol_bounds hc hlam hg hs hz).2.2)

/-- C2 (condition (6)): `den > 0` on `(0, ∞)` along a strictly decreasing solution. -/
lemma den_pos {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : ReinsPremium c cb) (hν : ClaimLaw ν)
    (hg : StrictAntiOn g (Ici 0)) (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0))
    {x : ℝ} (hx : 0 < x) : 0 < den c lam cb ν g x :=
  den_pos_of_continuousOn hc hlam hmu hsigma hg hs (den_continuousOn_sol hc hlam hcb hν hg hs) hx

/-! ### Bounds on the brackets near `0` (towards C3/C4) -/

/-- A bounded density `p ≤ P` gives `G(s) ≤ P s` for `s ≥ 0`. -/
lemma cdf_le_mul {ν : Measure ℝ} [IsProbabilityMeasure ν] (hneg : ν (Iic 0) = 0)
    {p : ℝ → ℝ} {P : ℝ} (hp : ∀ x, 0 ≤ p x ∧ p x ≤ P)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (p x))) {s : ℝ} (hs : 0 ≤ s) :
    cdf ν s ≤ P * s := by
  have hP : 0 ≤ P := le_trans (hp 0).1 (hp 0).2
  have h1 : ν (Iic s) ≤ ν (Iic 0) + ν (Ioc 0 s) := by
    rw [← Iic_union_Ioc_eq_Iic hs]
    exact measure_union_le _ _
  have h2 : ν (Ioc 0 s) ≤ ENNReal.ofReal (P * s) := by
    rw [hν, withDensity_apply _ measurableSet_Ioc]
    calc ∫⁻ x in Ioc 0 s, ENNReal.ofReal (p x) ≤ ∫⁻ x in Ioc 0 s, ENNReal.ofReal P :=
          lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hp x).2)
      _ = ENNReal.ofReal P * volume (Ioc 0 s) := setLIntegral_const _ _
      _ = ENNReal.ofReal (P * s) := by rw [Real.volume_Ioc, sub_zero, ENNReal.ofReal_mul hP]
  rw [hneg, zero_add] at h1
  rw [cdf_eq_real, measureReal_def]
  have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h1.trans h2)
  rwa [ENNReal.toReal_ofReal (mul_nonneg hP hs)] at h3

lemma phi_expand (c lam : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (g : ℝ → ℝ) (t b : ℝ) :
    phi c lam cb ν g t b = lam * tail ν t b + lam * conv ν g t b - c * g t + cb b * g t := by
  unfold phi conv; ring

lemma conv_nonneg {ν : Measure ℝ} [IsProbabilityMeasure ν] {g : ℝ → ℝ} {t b : ℝ} (ht : 0 ≤ t)
    (hg0 : ∀ z ∈ Icc (0:ℝ) t, 0 ≤ g z) : 0 ≤ conv ν g t b :=
  intervalIntegral.integral_nonneg ht (fun z hz => mul_nonneg (tail_nonneg ν _ _) (hg0 z hz))

/-- For `b ≥ b̲`: `φ_b(t) ≥ (λ - c g(t)) - λ P t / b̲`. -/
lemma phi_ge_low {c lam : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν] {g : ℝ → ℝ}
    (hlam : 0 < lam) (hcb : ReinsPremium c cb) {P bl : ℝ} (hP : 0 ≤ P) (hbl : 0 < bl)
    (hG : ∀ s, 0 ≤ s → cdf ν s ≤ P * s) {t : ℝ} (ht : 0 ≤ t)
    (hg0 : ∀ z ∈ Icc (0:ℝ) t, 0 ≤ g z) {b : ℝ} (hb : b ∈ Icc bl 1) :
    (lam - c * g t) - lam * P * t / bl ≤ phi c lam cb ν g t b := by
  have hbpos : 0 < b := lt_of_lt_of_le hbl hb.1
  have htail : tail ν t b = 1 - cdf ν (t / b) := by simp [tail, hbpos.ne']
  have h1 : cdf ν (t / b) ≤ P * t / bl := by
    calc cdf ν (t / b) ≤ P * (t / b) := hG (t / b) (div_nonneg ht hbpos.le)
      _ ≤ P * (t / bl) := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left ht hbl hb.1) hP
      _ = P * t / bl := by ring
  have h2 := conv_nonneg (ν := ν) (b := b) ht hg0
  have h3 : 0 ≤ cb b * g t := mul_nonneg (cb_nonneg hcb ⟨hbpos.le, hb.2⟩) (hg0 t ⟨ht, le_rfl⟩)
  have h4 := mul_le_mul_of_nonneg_left h1 hlam.le
  have h5 := mul_nonneg hlam.le h2
  rw [phi_expand, htail]
  have h6 : lam * (P * t / bl) = lam * P * t / bl := by ring
  nlinarith

/-- For `b < b̲` and small `t`: `φ_b(t) ≥ min (λ/2) ((c(b̲/2) - c) g(t))`. -/
lemma phi_ge_high {c lam : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν] {g : ℝ → ℝ}
    (hlam : 0 < lam) (hcb : ReinsPremium c cb) {P bl : ℝ} (hP : 0 ≤ P) (hbl : 0 < bl)
    (hbl1 : bl ≤ 1) (hblc : ∀ b ∈ Ico 0 bl, c < cb b)
    (hG : ∀ s, 0 ≤ s → cdf ν s ≤ P * s) {t : ℝ} (ht : 0 ≤ t) (hts : 2 * P * t ≤ bl / 2)
    (hg0 : ∀ z ∈ Icc (0:ℝ) t, 0 ≤ g z) {b : ℝ} (hb : b ∈ Ico 0 bl) :
    min (lam / 2) ((cb (bl / 2) - c) * g t) ≤ phi c lam cb ν g t b := by
  have h2 := conv_nonneg (ν := ν) (b := b) ht hg0
  have h5 := mul_nonneg hlam.le h2
  have hgt : 0 ≤ g t := hg0 t ⟨ht, le_rfl⟩
  have htl := tail_nonneg ν t b
  rw [phi_expand]
  rcases lt_or_ge b (bl / 2) with hb2 | hb2
  · have hanti : cb (bl / 2) ≤ cb b :=
      hcb.1 ⟨hb.1, by linarith⟩ ⟨by linarith, by linarith⟩ hb2.le
    have k1 : (cb (bl / 2) - c) * g t ≤ (cb b - c) * g t := mul_le_mul_of_nonneg_right (by linarith) hgt
    have k2 := mul_nonneg hlam.le htl
    refine (min_le_right _ _).trans ?_
    nlinarith
  · have hbpos : 0 < b := by linarith
    have htail : tail ν t b = 1 - cdf ν (t / b) := by simp [tail, hbpos.ne']
    have h1 : cdf ν (t / b) ≤ 1 / 2 := by
      have k := hG (t / b) (div_nonneg ht hbpos.le)
      have k' : P * (t / b) ≤ 1 / 2 := by
        rw [mul_div_assoc', div_le_iff₀ hbpos]
        nlinarith
      linarith
    have hcbb : c < cb b := hblc b hb
    have k3 : 0 ≤ (cb b - c) * g t := mul_nonneg (by linarith) hgt
    rw [htail]
    refine (min_le_left _ _).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left h1 hlam.le]

/-- Upper bound: `den(t) ≤ (λ - c g(t)) + λ M t` when `0 ≤ g ≤ M` on `[0,t]` and `g t ≤ λ/c`. -/
lemma den_le_upper {c lam : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν] {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hcb : ReinsPremium c cb) {M t : ℝ} (ht : 0 ≤ t)
    (hgc : ContinuousOn g (Icc 0 t))
    (hg0 : ∀ z ∈ Icc (0:ℝ) t, 0 ≤ g z) (hgM : ∀ z ∈ Icc (0:ℝ) t, g z ≤ M)
    (hgt : g t ≤ lam / c) :
    den c lam cb ν g t ≤ (lam - c * g t) + lam * M * t := by
  have hd := den_le_phi (ν := ν) (g := g) (cb := cb) hc hlam hcb ht hg0 hgt
    (⟨zero_le_one, le_rfl⟩ : (1:ℝ) ∈ Icc (0:ℝ) 1)
  have hc0 := conv_sub_le (ν := ν) (g := g) (M := M) (b := 1) zero_le_one le_rfl ht hgc hg0 hgM
  have hconv0 : conv ν g 0 1 = 0 := by simp [conv]
  rw [hconv0, sub_zero, sub_zero] at hc0
  have hcv : conv ν g t 1 ≤ M * t := (abs_le.1 hc0).2
  rw [phi_expand, hcb.2.2.1] at hd
  have k1 := tail_le_one ν t 1
  nlinarith [mul_le_mul_of_nonneg_left hcv hlam.le, mul_le_mul_of_nonneg_left k1 hlam.le]

/-- Splitting the infimum: lower bounds on `b < b̲` and on `b ≥ b̲` give `den ≥ min`. -/
lemma den_ge_min {c lam : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ} {bl t m L : ℝ}
    (hlow : ∀ b ∈ Ico (0:ℝ) bl, m ≤ phi c lam cb ν g t b)
    (hhigh : ∀ b ∈ Icc bl 1, L ≤ phi c lam cb ν g t b) :
    min m L ≤ den c lam cb ν g t := by
  rw [den_eq_sInf_phi]
  refine le_csInf ((nonempty_Icc.2 zero_le_one).image _) ?_
  rintro _ ⟨b, hb, rfl⟩
  rcases lt_or_ge b bl with h | h
  · exact (min_le_left _ _).trans (hlow b ⟨hb.1, h⟩)
  · exact (min_le_right _ _).trans (hhigh b ⟨h, hb.2⟩)


/-! ### C3: square-root lower bound near `0` -/

lemma I_strictMono {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hg : StrictAntiOn g (Ici 0)) (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0))
    {t x : ℝ} (ht : 0 ≤ t) (htx : t < x) :
    (∫ u in (0:ℝ)..t, (den c lam cb ν g u)⁻¹) < ∫ u in (0:ℝ)..x, (den c lam cb ν g u)⁻¹ := by
  have h := yfun_strictMonoOn hc hlam hg hs (mem_Ici.2 ht) (mem_Ici.2 (ht.trans htx.le)) htx
  unfold yfun at h
  have hK : 0 < mu ^ 2 / (2 * sigma ^ 2) := by positivity
  exact lt_of_mul_lt_mul_left (by linarith) hK.le

/-- `λ - c g(t) = λ K I(t) / y(t)` and `I(t) ≥ 0`. -/
lemma lam_sub_cg {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hg : StrictAntiOn g (Ici 0)) (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0))
    {t : ℝ} (ht : 0 ≤ t) :
    lam - c * g t = lam * (mu ^ 2 / (2 * sigma ^ 2)) * (∫ u in (0:ℝ)..t, (den c lam cb ν g u)⁻¹)
      / yfun c lam mu sigma cb ν g t ∧ 0 ≤ ∫ u in (0:ℝ)..t, (den c lam cb ν g u)⁻¹ := by
  have hb := sol_bounds hc hlam hg hs ht
  have hY : 0 < yfun c lam mu sigma cb ν g t := lt_of_lt_of_le (div_pos hc hlam) hb.1
  have hYdef : yfun c lam mu sigma cb ν g t =
      mu ^ 2 / (2 * sigma ^ 2) * (∫ u in (0:ℝ)..t, (den c lam cb ν g u)⁻¹) + c / lam := rfl
  have hK : 0 < mu ^ 2 / (2 * sigma ^ 2) := by positivity
  refine ⟨?_, ?_⟩
  · rw [g_eq_inv_yfun hs ht, eq_div_iff hY.ne', sub_mul, mul_assoc c, one_div_mul_cancel hY.ne',
      mul_one]
    have e : lam * (c / lam) = c := by field_simp
    rw [hYdef]
    linear_combination e
  · have h1 : 0 ≤ mu ^ 2 / (2 * sigma ^ 2) * (∫ u in (0:ℝ)..t, (den c lam cb ν g u)⁻¹) := by
      linarith [hb.1]
    exact (mul_nonneg_iff_of_pos_left hK).1 h1

/-- `λ - c g(t) ≤ (λ² K / c) I(t)`. -/
lemma lam_sub_cg_le {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hg : StrictAntiOn g (Ici 0)) (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0))
    {t : ℝ} (ht : 0 ≤ t) :
    lam - c * g t ≤ lam ^ 2 * (mu ^ 2 / (2 * sigma ^ 2)) / c *
      ∫ u in (0:ℝ)..t, (den c lam cb ν g u)⁻¹ := by
  obtain ⟨heq, hI⟩ := lam_sub_cg hc hlam hmu hsigma hg hs ht
  have hb := sol_bounds hc hlam hg hs ht
  have hK : 0 < mu ^ 2 / (2 * sigma ^ 2) := by positivity
  rw [heq]
  have hnum : 0 ≤ lam * (mu ^ 2 / (2 * sigma ^ 2)) * (∫ u in (0:ℝ)..t, (den c lam cb ν g u)⁻¹) :=
    mul_nonneg (mul_nonneg hlam.le hK.le) hI
  calc _ ≤ lam * (mu ^ 2 / (2 * sigma ^ 2)) * (∫ u in (0:ℝ)..t, (den c lam cb ν g u)⁻¹) / (c / lam) :=
        div_le_div_of_nonneg_left hnum (div_pos hc hlam) hb.1
    _ = _ := by field_simp

/-- `I(x) ≥ κ √x` on `(0, 1]`. -/
lemma I_sqrt_lower {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : ReinsPremium c cb) (hν : ClaimLaw ν)
    (hg : StrictAntiOn g (Ici 0)) (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0)) :
    ∃ κ > 0, ∀ x ∈ Ioc (0:ℝ) 1,
      κ * Real.sqrt x ≤ ∫ t in (0:ℝ)..x, (den c lam cb ν g t)⁻¹ := by
  have := hν.1
  have hKpos : 0 < mu ^ 2 / (2 * sigma ^ 2) := by positivity
  obtain ⟨B1, hB1⟩ : ∃ B1, B1 = lam ^ 2 * (mu ^ 2 / (2 * sigma ^ 2)) / c := ⟨_, rfl⟩
  obtain ⟨B2, hB2⟩ : ∃ B2, B2 = lam ^ 2 / c := ⟨_, rfl⟩
  have hB1pos : 0 < B1 := by rw [hB1]; positivity
  have hB2pos : 0 < B2 := by rw [hB2]; positivity
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = 1 / (2 * (B1 + B2 + 1)) := ⟨_, rfl⟩
  have hκpos : 0 < κ := by rw [hκ]; positivity
  have hκ1 : κ * (B1 + B2) ≤ 1 / 2 := by
    rw [hκ, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hκle : κ ≤ 1 := by
    rw [hκ, div_le_one (by positivity)]; linarith
  refine ⟨κ, hκpos, fun x hx => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt x := ⟨_, rfl⟩
  rw [← hsdef] at hlt
  have hspos : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 hx.1
  have hs1 : s ≤ 1 := by rw [hsdef]; exact Real.sqrt_le_one.2 hx.2
  have hss : s * s = x := by rw [hsdef]; exact Real.mul_self_sqrt hx.1.le
  obtain ⟨D, hD⟩ : ∃ D, D = B1 * κ * s + B2 * (s * s) := ⟨_, rfl⟩
  have hDpos : 0 < D := by rw [hD]; positivity
  have hpt : ∀ t ∈ Ioo (0:ℝ) x, D⁻¹ ≤ (den c lam cb ν g t)⁻¹ := by
    intro t ht
    have hdpos := den_pos hc hlam hmu hsigma hcb hν hg hs ht.1
    have hb := sol_bounds hc hlam hg hs ht.1.le
    have hup := den_le_upper (ν := ν) (g := g) (cb := cb) (M := lam / c) hc hlam hcb ht.1.le
      (sol_continuousOn hc hlam hg hs ht.1.le)
      (fun z hz => (sol_bounds hc hlam hg hs hz.1).2.1.le)
      (fun z hz => (sol_bounds hc hlam hg hs hz.1).2.2) hb.2.2
    have hlc := lam_sub_cg_le hc hlam hmu hsigma hg hs ht.1.le
    have hIt := I_strictMono hc hlam hmu hsigma hg hs ht.1.le ht.2
    rw [← hB1] at hlc
    have k1 : B1 * (∫ u in (0:ℝ)..t, (den c lam cb ν g u)⁻¹) ≤ B1 * (κ * s) :=
      mul_le_mul_of_nonneg_left (by linarith) hB1pos.le
    have k2 : lam * (lam / c) * t = B2 * t := by rw [hB2]; ring
    have k3 : B2 * t ≤ B2 * (s * s) := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hB2pos.le
    have hden : den c lam cb ν g t ≤ D := by
      rw [hD]; nlinarith
    exact inv_anti₀ hdpos hden
  have hint : IntervalIntegrable (fun t => (den c lam cb ν g t)⁻¹) volume 0 x :=
    (hs x hx.1.le).2.2.1
  have hI := intervalIntegral.integral_mono_on_of_le_Ioo hx.1.le intervalIntegrable_const hint hpt
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hI
  have hfin : κ * s ≤ x * D⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hDpos, ← hss, hD]
    have k1 : κ * B1 * κ + κ * B2 * s ≤ 1 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hκle (le_of_lt (mul_pos hκpos hB1pos)),
        mul_le_mul_of_nonneg_left hs1 (le_of_lt (mul_pos hκpos hB2pos))]
    have k2 : κ * s * (B1 * κ * s + B2 * (s * s)) = s * s * (κ * B1 * κ + κ * B2 * s) := by ring
    rw [k2]
    have k3 : 0 < s * s := mul_pos hspos hspos
    nlinarith
  linarith


/-- C3: `den(t) ≥ α √t` on `(0, x₀]` (bounded density). -/
lemma den_sqrt_lower {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : ReinsPremium c cb) (hν : ClaimLaw ν) (hdens : SchmidliRuin.Exist.HasBoundedDensity ν)
    (hg : StrictAntiOn g (Ici 0)) (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0)) :
    ∃ α > 0, ∃ x₀ > 0, x₀ ≤ 1 ∧ ∀ t ∈ Ioc 0 x₀, α * Real.sqrt t ≤ den c lam cb ν g t := by
  have := hν.1
  obtain ⟨p, -, ⟨P, hp⟩, hνeq⟩ := hdens
  have hP : 0 ≤ P := le_trans (hp 0).1 (hp 0).2
  have hG : ∀ s, 0 ≤ s → cdf ν s ≤ P * s := fun s hs0 => cdf_le_mul hν.2.1 hp hνeq hs0
  obtain ⟨bl, hbl, hbl1, hblc, -⟩ := hcb.2.2.2.2
  obtain ⟨κ, hκ, hI⟩ := I_sqrt_lower hc hlam hmu hsigma hcb hν hg hs
  have hKpos : 0 < mu ^ 2 / (2 * sigma ^ 2) := by positivity
  have hb1 := sol_bounds hc hlam hg hs zero_le_one
  have hY1 : 0 < yfun c lam mu sigma cb ν g 1 := lt_of_lt_of_le (div_pos hc hlam) hb1.1
  obtain ⟨a, ha⟩ : ∃ a, a = lam * (mu ^ 2 / (2 * sigma ^ 2)) / yfun c lam mu sigma cb ν g 1 :=
    ⟨_, rfl⟩
  have hapos : 0 < a := by rw [ha]; positivity
  have hcbl : c < cb (bl / 2) := hblc (bl / 2) ⟨by linarith, by linarith⟩
  obtain ⟨m, hm⟩ : ∃ m, m = min (lam / 2) ((cb (bl / 2) - c) * g 1) := ⟨_, rfl⟩
  have hmpos : 0 < m := by
    rw [hm]; exact lt_min (by linarith) (mul_pos (by linarith) hb1.2.1)
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = min 1 (min (bl / (4 * (P + 1)))
      (min (a * κ * bl / (2 * lam * (P + 1))) (2 * m / (a * κ)))) := ⟨_, rfl⟩
  have hs0pos : 0 < s0 := by
    rw [hs0]
    exact lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hs0_1 : s0 ≤ 1 := by rw [hs0]; exact min_le_left _ _
  have hs0_2 : s0 ≤ bl / (4 * (P + 1)) := by
    rw [hs0]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hs0_3 : s0 ≤ a * κ * bl / (2 * lam * (P + 1)) := by
    rw [hs0]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs0_4 : s0 ≤ 2 * m / (a * κ) := by
    rw [hs0]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨a * κ / 2, by positivity, s0 * s0, mul_pos hs0pos hs0pos, by nlinarith, fun t ht => ?_⟩
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt t := ⟨_, rfl⟩
  rw [← hsdef]
  have hspos : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 ht.1
  have hss : s * s = t := by rw [hsdef]; exact Real.mul_self_sqrt ht.1.le
  have hss0 : s ≤ s0 := by
    rw [hsdef]
    calc Real.sqrt t ≤ Real.sqrt (s0 * s0) := Real.sqrt_le_sqrt ht.2
      _ = s0 := Real.sqrt_mul_self hs0pos.le
  have ht1 : t ≤ 1 := by nlinarith
  have ht0 : 0 ≤ t := ht.1.le
  have hg0 : ∀ z ∈ Icc (0:ℝ) t, 0 ≤ g z := fun z hz => (sol_bounds hc hlam hg hs hz.1).2.1.le
  have hts : 2 * P * t ≤ bl / 2 := by
    have k1 : t ≤ s := by nlinarith
    have k2 : s * (4 * (P + 1)) ≤ bl :=
      (le_div_iff₀ (by positivity : (0:ℝ) < 4 * (P + 1))).1 (hss0.trans hs0_2)
    nlinarith [mul_le_mul_of_nonneg_left k1 hP]
  have hgt1 : g 1 ≤ g t := hg.antitoneOn (mem_Ici.2 ht0) (mem_Ici.2 zero_le_one) ht1
  have hlow : ∀ b ∈ Ico (0:ℝ) bl, m ≤ phi c lam cb ν g t b := by
    intro b hb
    have k := phi_ge_high (ν := ν) (g := g) hlam hcb hP hbl hbl1 hblc hG ht0 hts hg0 hb
    have k2 : m ≤ min (lam / 2) ((cb (bl / 2) - c) * g t) := by
      rw [hm]; exact min_le_min le_rfl (mul_le_mul_of_nonneg_left hgt1 (by linarith))
    exact k2.trans k
  have hlc : a * κ * s ≤ lam - c * g t := by
    obtain ⟨heq, hI0⟩ := lam_sub_cg hc hlam hmu hsigma hg hs ht0
    have hIt := hI t ⟨ht.1, ht1⟩
    rw [← hsdef] at hIt
    have hYt := sol_bounds hc hlam hg hs ht0
    have hYtpos : 0 < yfun c lam mu sigma cb ν g t := lt_of_lt_of_le (div_pos hc hlam) hYt.1
    have hYle : yfun c lam mu sigma cb ν g t ≤ yfun c lam mu sigma cb ν g 1 :=
      (yfun_strictMonoOn hc hlam hg hs).monotoneOn (mem_Ici.2 ht0) (mem_Ici.2 zero_le_one) ht1
    rw [heq]
    have hnum : 0 ≤ lam * (mu ^ 2 / (2 * sigma ^ 2)) *
        (∫ u in (0:ℝ)..t, (den c lam cb ν g u)⁻¹) := mul_nonneg (by positivity) hI0
    calc a * κ * s = lam * (mu ^ 2 / (2 * sigma ^ 2)) * (κ * s) / yfun c lam mu sigma cb ν g 1 := by
          rw [ha]; ring
      _ ≤ lam * (mu ^ 2 / (2 * sigma ^ 2)) * (∫ u in (0:ℝ)..t, (den c lam cb ν g u)⁻¹)
            / yfun c lam mu sigma cb ν g 1 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hIt (by positivity)) hY1.le
      _ ≤ _ := div_le_div_of_nonneg_left hnum hYtpos hYle
  have hhigh : ∀ b ∈ Icc bl 1, a * κ * s / 2 ≤ phi c lam cb ν g t b := by
    intro b hb
    have k := phi_ge_low (ν := ν) (g := g) (cb := cb) (c := c) hlam hcb hP hbl hG ht0 hg0 hb
    have k2 : lam * P * t / bl ≤ a * κ * s / 2 := by
      rw [div_le_iff₀ hbl]
      have k3 : s * (2 * lam * (P + 1)) ≤ a * κ * bl :=
        (le_div_iff₀ (by positivity : (0:ℝ) < 2 * lam * (P + 1))).1 (hss0.trans hs0_3)
      rw [← hss]
      nlinarith [mul_le_mul_of_nonneg_left k3 hspos.le,
        mul_nonneg (mul_nonneg hlam.le hspos.le) hspos.le]
    linarith
  have hfin := den_ge_min hlow hhigh
  have hm2 : a * κ * s / 2 ≤ m := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < a * κ)).1 (hss0.trans hs0_4)
    linarith
  calc a * κ / 2 * s = min m (a * κ * s / 2) := by rw [min_eq_right hm2]; ring
    _ ≤ _ := hfin


/-! ### C4: local uniqueness at `0` -/

/-- Difference of two solutions: `|g₁ - g₂| ≤ K (λ/c)² |I₁ - I₂|`, and `I₁ ≥ I₂ → g₁ ≤ g₂`. -/
lemma g_diff {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g1 g2 : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hg1 : StrictAntiOn g1 (Ici 0)) (hs1 : SolvesEq5On c lam mu sigma cb ν g1 (Ici 0))
    (hg2 : StrictAntiOn g2 (Ici 0)) (hs2 : SolvesEq5On c lam mu sigma cb ν g2 (Ici 0))
    {z : ℝ} (hz : 0 ≤ z) :
    |g1 z - g2 z| ≤ mu ^ 2 / (2 * sigma ^ 2) * (lam / c) ^ 2 *
        |(∫ u in (0:ℝ)..z, (den c lam cb ν g1 u)⁻¹) - ∫ u in (0:ℝ)..z, (den c lam cb ν g2 u)⁻¹| ∧
      (0 ≤ (∫ u in (0:ℝ)..z, (den c lam cb ν g1 u)⁻¹) - ∫ u in (0:ℝ)..z, (den c lam cb ν g2 u)⁻¹ →
        g1 z ≤ g2 z) := by
  have hb1 := sol_bounds hc hlam hg1 hs1 hz
  have hb2 := sol_bounds hc hlam hg2 hs2 hz
  have hcl : 0 < c / lam := div_pos hc hlam
  have hY1 : 0 < yfun c lam mu sigma cb ν g1 z := lt_of_lt_of_le hcl hb1.1
  have hY2 : 0 < yfun c lam mu sigma cb ν g2 z := lt_of_lt_of_le hcl hb2.1
  have hK : 0 < mu ^ 2 / (2 * sigma ^ 2) := by positivity
  have hYd : yfun c lam mu sigma cb ν g1 z - yfun c lam mu sigma cb ν g2 z =
      mu ^ 2 / (2 * sigma ^ 2) * ((∫ u in (0:ℝ)..z, (den c lam cb ν g1 u)⁻¹)
        - ∫ u in (0:ℝ)..z, (den c lam cb ν g2 u)⁻¹) := by
    unfold yfun; ring
  rw [g_eq_inv_yfun hs1 hz, g_eq_inv_yfun hs2 hz]
  refine ⟨?_, fun hδ => ?_⟩
  · have e : 1 / yfun c lam mu sigma cb ν g1 z - 1 / yfun c lam mu sigma cb ν g2 z =
        -(yfun c lam mu sigma cb ν g1 z - yfun c lam mu sigma cb ν g2 z) /
          (yfun c lam mu sigma cb ν g1 z * yfun c lam mu sigma cb ν g2 z) := by
      field_simp; ring
    rw [e, hYd, abs_div, abs_neg, abs_mul, abs_of_pos hK, abs_of_pos (mul_pos hY1 hY2)]
    have hnum : 0 ≤ mu ^ 2 / (2 * sigma ^ 2) *
        |(∫ u in (0:ℝ)..z, (den c lam cb ν g1 u)⁻¹) - ∫ u in (0:ℝ)..z, (den c lam cb ν g2 u)⁻¹| :=
      mul_nonneg hK.le (abs_nonneg _)
    have hprod : c / lam * (c / lam) ≤
        yfun c lam mu sigma cb ν g1 z * yfun c lam mu sigma cb ν g2 z :=
      mul_le_mul hb1.1 hb2.1 hcl.le hY1.le
    calc _ ≤ mu ^ 2 / (2 * sigma ^ 2) *
          |(∫ u in (0:ℝ)..z, (den c lam cb ν g1 u)⁻¹) - ∫ u in (0:ℝ)..z, (den c lam cb ν g2 u)⁻¹|
          / (c / lam * (c / lam)) := div_le_div_of_nonneg_left hnum (mul_pos hcl hcl) hprod
      _ = _ := by field_simp
  · have hle : yfun c lam mu sigma cb ν g2 z ≤ yfun c lam mu sigma cb ν g1 z := by
      have := mul_nonneg hK.le hδ
      linarith
    exact one_div_le_one_div_of_le hY2 hle

lemma conv_diff {ν : Measure ℝ} [IsProbabilityMeasure ν] {g1 g2 : ℝ → ℝ} {t b B : ℝ}
    (ht : 0 ≤ t) (hb : 0 ≤ b)
    (hc1 : ContinuousOn g1 (Icc 0 t)) (hc2 : ContinuousOn g2 (Icc 0 t))
    (hB : ∀ z ∈ Icc (0:ℝ) t, |g1 z - g2 z| ≤ B) :
    |conv ν g1 t b - conv ν g2 t b| ≤ B * t := by
  have hI1 : IntervalIntegrable (fun z => tail ν (t - z) b * g1 z) volume 0 t :=
    (tail_sub_intervalIntegrable ν hb t 0 t).mul_continuousOn (by rwa [uIcc_of_le ht])
  have hI2 : IntervalIntegrable (fun z => tail ν (t - z) b * g2 z) volume 0 t :=
    (tail_sub_intervalIntegrable ν hb t 0 t).mul_continuousOn (by rwa [uIcc_of_le ht])
  unfold conv
  rw [← intervalIntegral.integral_sub hI1 hI2]
  have key := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := t) (C := B)
    (f := fun z => tail ν (t - z) b * g1 z - tail ν (t - z) b * g2 z) (fun z hz => by
      rw [uIoc_of_le ht] at hz
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (tail_nonneg ν _ _)]
      calc tail ν (t - z) b * |g1 z - g2 z| ≤ 1 * B :=
            mul_le_mul (tail_le_one ν _ _) (hB z ⟨hz.1.le, hz.2⟩) (abs_nonneg _) zero_le_one
        _ = B := one_mul B)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at key
  exact key

/-- `den` of a solution is small near `0`. -/
lemma den_small {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hcb : ReinsPremium c cb) (hν : ClaimLaw ν)
    (hg : StrictAntiOn g (Ici 0)) (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0))
    {m : ℝ} (hm : 0 < m) : ∃ τ > 0, ∀ t ∈ Ioc (0:ℝ) τ, den c lam cb ν g t < m := by
  have := hν.1
  have hg0 : g 0 = lam / c := by rw [g_eq_inv_yfun hs le_rfl, yfun_zero, one_div_div]
  have hgc := sol_continuousOn_Ici hc hlam hg hs 0 (mem_Ici.2 le_rfl)
  obtain ⟨η, hη, hηb⟩ := Metric.continuousWithinAt_iff.1 hgc (m / (2 * c)) (by positivity)
  refine ⟨min (η / 2) (m * c / (4 * lam ^ 2)), lt_min (by positivity) (by positivity),
    fun t ht => ?_⟩
  have ht0 : 0 ≤ t := ht.1.le
  have hb := sol_bounds hc hlam hg hs ht0
  have hup := den_le_upper (ν := ν) (g := g) (cb := cb) (M := lam / c) hc hlam hcb ht0
      (sol_continuousOn hc hlam hg hs ht0)
      (fun z hz => (sol_bounds hc hlam hg hs hz.1).2.1.le)
      (fun z hz => (sol_bounds hc hlam hg hs hz.1).2.2) hb.2.2
  have hd : dist t 0 < η := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht0]
    linarith [ht.2.trans (min_le_left _ _)]
  have k := hηb (mem_Ici.2 ht0) hd
  rw [Real.dist_eq, hg0] at k
  have k1 : lam - c * g t < m / 2 := by
    have k0 := mul_lt_mul_of_pos_left (abs_lt.1 k).1 hc
    have e : c * (m / (2 * c)) = m / 2 := by field_simp
    have e2 : c * (lam / c) = lam := by field_simp
    rw [mul_sub, e2, mul_neg, e] at k0
    linarith
  have k2 : lam * (lam / c) * t ≤ m / 4 := by
    have ht2 : t ≤ m * c / (4 * lam ^ 2) := ht.2.trans (min_le_right _ _)
    have e : lam * (lam / c) * (m * c / (4 * lam ^ 2)) = m / 4 := by field_simp; try ring
    have k3 := mul_le_mul_of_nonneg_left ht2 (by positivity : (0:ℝ) ≤ lam * (lam / c))
    linarith
  linarith


/-- One-sided comparison of the integrands near `0`. -/
lemma inv_den_cmp {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g1 g2 : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : ReinsPremium c cb) (hν : ClaimLaw ν) (hdens : SchmidliRuin.Exist.HasBoundedDensity ν)
    (hg1 : StrictAntiOn g1 (Ici 0)) (hs1 : SolvesEq5On c lam mu sigma cb ν g1 (Ici 0))
    (hg2 : StrictAntiOn g2 (Ici 0)) (hs2 : SolvesEq5On c lam mu sigma cb ν g2 (Ici 0)) :
    ∃ τ > 0, ∃ C > 0, ∀ t ∈ Ioc (0:ℝ) τ, ∀ M : ℝ,
      (∀ z ∈ Icc (0:ℝ) t, |(∫ u in (0:ℝ)..z, (den c lam cb ν g1 u)⁻¹)
        - ∫ u in (0:ℝ)..z, (den c lam cb ν g2 u)⁻¹| ≤ M) →
      0 ≤ (∫ u in (0:ℝ)..t, (den c lam cb ν g1 u)⁻¹) - ∫ u in (0:ℝ)..t, (den c lam cb ν g2 u)⁻¹ →
      (den c lam cb ν g1 t)⁻¹ - (den c lam cb ν g2 t)⁻¹ ≤ C * M := by
  have := hν.1
  obtain ⟨α1, hα1, x1, hx1, hx11, hden1⟩ :=
    den_sqrt_lower hc hlam hmu hsigma hcb hν hdens hg1 hs1
  obtain ⟨α2, hα2, x2, hx2, hx21, hden2⟩ :=
    den_sqrt_lower hc hlam hmu hsigma hcb hν hdens hg2 hs2
  obtain ⟨p, -, ⟨P, hp⟩, hνeq⟩ := hdens
  have hP : 0 ≤ P := le_trans (hp 0).1 (hp 0).2
  have hG : ∀ s, 0 ≤ s → cdf ν s ≤ P * s := fun s hs0 => cdf_le_mul hν.2.1 hp hνeq hs0
  obtain ⟨bl, hbl, hbl1, hblc, hblh⟩ := hcb.2.2.2.2
  have hcbl : c < cb (bl / 2) := hblc (bl / 2) ⟨by linarith, by linarith⟩
  have hb11 := sol_bounds hc hlam hg1 hs1 zero_le_one
  obtain ⟨m, hm⟩ : ∃ m, m = min (lam / 2) ((cb (bl / 2) - c) * g1 1) := ⟨_, rfl⟩
  have hmpos : 0 < m := by
    rw [hm]; exact lt_min (by linarith) (mul_pos (by linarith) hb11.2.1)
  obtain ⟨τ3, hτ3, hsmall⟩ := den_small hc hlam hcb hν hg2 hs2 hmpos
  have hKpos : 0 < mu ^ 2 / (2 * sigma ^ 2) := by positivity
  obtain ⟨L, hL⟩ : ∃ L, L = mu ^ 2 / (2 * sigma ^ 2) * (lam / c) ^ 2 := ⟨_, rfl⟩
  have hLpos : 0 < L := by rw [hL]; positivity
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = min (min x1 x2) (min τ3 (bl / (4 * (P + 1)))) := ⟨_, rfl⟩
  have hτpos : 0 < τ := by
    rw [hτ]; exact lt_min (lt_min hx1 hx2) (lt_min hτ3 (by positivity))
  refine ⟨τ, hτpos, lam * L / (α1 * α2), by positivity, fun t ht M hM hδt => ?_⟩
  have htpos : 0 < t := ht.1
  have htx1 : t ≤ x1 :=
    ht.2.trans (by rw [hτ]; exact (min_le_left _ _).trans (min_le_left _ _))
  have htx2 : t ≤ x2 :=
    ht.2.trans (by rw [hτ]; exact (min_le_left _ _).trans (min_le_right _ _))
  have htτ3 : t ≤ τ3 :=
    ht.2.trans (by rw [hτ]; exact (min_le_right _ _).trans (min_le_left _ _))
  have htP : t ≤ bl / (4 * (P + 1)) :=
    ht.2.trans (by rw [hτ]; exact (min_le_right _ _).trans (min_le_right _ _))
  have ht0 : 0 ≤ t := ht.1.le
  have ht1 : t ≤ 1 := htx1.trans hx11
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t ⟨ht0, le_rfl⟩)
  have hts : 2 * P * t ≤ bl / 2 := by
    have k2 : t * (4 * (P + 1)) ≤ bl :=
      (le_div_iff₀ (by positivity : (0:ℝ) < 4 * (P + 1))).1 htP
    nlinarith
  have hg10 : ∀ z ∈ Icc (0:ℝ) t, 0 ≤ g1 z := fun z hz => (sol_bounds hc hlam hg1 hs1 hz.1).2.1.le
  have hg20 : ∀ z ∈ Icc (0:ℝ) t, 0 ≤ g2 z := fun z hz => (sol_bounds hc hlam hg2 hs2 hz.1).2.1.le
  have hgd : ∀ z ∈ Icc (0:ℝ) t, |g1 z - g2 z| ≤ L * M := by
    intro z hz
    have k := (g_diff hc hlam hmu hsigma hg1 hs1 hg2 hs2 hz.1).1
    rw [← hL] at k
    exact k.trans (mul_le_mul_of_nonneg_left (hM z hz) hLpos.le)
  have hsign : g1 t ≤ g2 t := (g_diff hc hlam hmu hsigma hg1 hs1 hg2 hs2 ht0).2 hδt
  have hcv : ∀ b ∈ Icc (0:ℝ) 1, |conv ν g1 t b - conv ν g2 t b| ≤ L * M * t := fun b hb =>
    conv_diff ht0 hb.1 (sol_continuousOn hc hlam hg1 hs1 ht0)
      (sol_continuousOn hc hlam hg2 hs2 ht0) hgd
  have hgt1 : g1 1 ≤ g1 t := hg1.antitoneOn (mem_Ici.2 ht0) (mem_Ici.2 zero_le_one) ht1
  have hlow : ∀ b ∈ Ico (0:ℝ) bl, m ≤ phi c lam cb ν g1 t b := by
    intro b hb
    have k := phi_ge_high (ν := ν) (g := g1) hlam hcb hP hbl hbl1 hblc hG ht0 hts hg10 hb
    have k2 : m ≤ min (lam / 2) ((cb (bl / 2) - c) * g1 t) := by
      rw [hm]; exact min_le_min le_rfl (mul_le_mul_of_nonneg_left hgt1 (by linarith))
    exact k2.trans k
  have hb2t := sol_bounds hc hlam hg2 hs2 ht0
  have hhigh : ∀ b ∈ Icc bl 1,
      den c lam cb ν g2 t - lam * (L * M * t) ≤ phi c lam cb ν g1 t b := by
    intro b hb
    have hb01 : b ∈ Icc (0:ℝ) 1 := ⟨hbl.le.trans hb.1, hb.2⟩
    have k1 := den_le_phi (ν := ν) (g := g2) (cb := cb) hc hlam hcb ht0 hg20 hb2t.2.2 hb01
    have k2 := (abs_le.1 (hcv b hb01)).1
    have k3 : 0 ≤ (c - cb b) * (g2 t - g1 t) :=
      mul_nonneg (by linarith [hblh b hb]) (by linarith)
    rw [phi_expand] at k1 ⊢
    nlinarith [mul_le_mul_of_nonneg_left k2 hlam.le]
  have hmin := den_ge_min hlow hhigh
  have hd2small := hsmall t ⟨ht.1, htτ3⟩
  have hLMt : 0 ≤ lam * (L * M * t) := by positivity
  have hd1 : den c lam cb ν g2 t - lam * (L * M * t) ≤ den c lam cb ν g1 t := by
    rw [min_eq_right (by linarith)] at hmin; exact hmin
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0
  have hl1 := hden1 t ⟨ht.1, htx1⟩
  have hl2 := hden2 t ⟨ht.1, htx2⟩
  have hp1 : 0 < den c lam cb ν g1 t := lt_of_lt_of_le (by positivity) hl1
  have hp2 : 0 < den c lam cb ν g2 t := lt_of_lt_of_le (by positivity) hl2
  have hprod : α1 * α2 * t ≤ den c lam cb ν g1 t * den c lam cb ν g2 t := by
    calc α1 * α2 * t = α1 * α2 * (Real.sqrt t * Real.sqrt t) := by rw [hsq]
      _ = (α1 * Real.sqrt t) * (α2 * Real.sqrt t) := by ring
      _ ≤ _ := mul_le_mul hl1 hl2 (by positivity) hp1.le
  rw [inv_sub_inv hp1.ne' hp2.ne']
  have hpp : 0 < den c lam cb ν g1 t * den c lam cb ν g2 t := mul_pos hp1 hp2
  calc (den c lam cb ν g2 t - den c lam cb ν g1 t) / (den c lam cb ν g1 t * den c lam cb ν g2 t)
      ≤ lam * (L * M * t) / (den c lam cb ν g1 t * den c lam cb ν g2 t) :=
        div_le_div_of_nonneg_right (by linarith) hpp.le
    _ ≤ lam * (L * M * t) / (α1 * α2 * t) :=
        div_le_div_of_nonneg_left hLMt (by positivity) hprod
    _ = lam * L / (α1 * α2) * M := by field_simp

/-- Abstract one-sided bound: if `δ(0) = 0`, `δ' = f` and `f ≤ B` wherever `δ > 0`, then
`δ ≤ ε B` on `[0, ε]`. -/
lemma one_sided_bound {δ f : ℝ → ℝ} {ε B : ℝ} (hB : 0 ≤ B)
    (hδc : ContinuousOn δ (Icc 0 ε)) (hδ0 : δ 0 = 0)
    (hint : IntervalIntegrable f volume 0 ε)
    (hFTC : ∀ a b, 0 ≤ a → a ≤ b → b ≤ ε → δ b - δ a = ∫ t in a..b, f t)
    (hf : ∀ t ∈ Ioo 0 ε, 0 < δ t → f t ≤ B) :
    ∀ x ∈ Icc 0 ε, δ x ≤ ε * B := by
  intro x hx
  have hε : 0 ≤ ε := hx.1.trans hx.2
  by_cases hpos : δ x ≤ 0
  · exact hpos.trans (mul_nonneg hε hB)
  push Not at hpos
  have hcl : IsClosed (Icc 0 x ∩ δ ⁻¹' Iic 0) :=
    (hδc.mono (Icc_subset_Icc le_rfl hx.2)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hcpt : IsCompact (Icc 0 x ∩ δ ⁻¹' Iic 0) :=
    isCompact_Icc.of_isClosed_subset hcl inter_subset_left
  have h0S : (0:ℝ) ∈ Icc 0 x ∩ δ ⁻¹' Iic 0 := ⟨⟨le_rfl, hx.1⟩, by simp [hδ0]⟩
  have hx'S := hcpt.sSup_mem ⟨0, h0S⟩
  have hbdd := hcpt.bddAbove
  have hx'0 : 0 ≤ sSup (Icc 0 x ∩ δ ⁻¹' Iic 0) := le_csSup hbdd h0S
  have hx'x : sSup (Icc 0 x ∩ δ ⁻¹' Iic 0) ≤ x := hx'S.1.2
  have hδx' : δ (sSup (Icc 0 x ∩ δ ⁻¹' Iic 0)) ≤ 0 := hx'S.2
  have hpos' : ∀ t ∈ Ioo (sSup (Icc 0 x ∩ δ ⁻¹' Iic 0)) x, 0 < δ t := by
    intro t ht
    by_contra hle
    push Not at hle
    have hmem : t ∈ Icc 0 x ∩ δ ⁻¹' Iic 0 := ⟨⟨hx'0.trans ht.1.le, ht.2.le⟩, hle⟩
    have := le_csSup hbdd hmem
    linarith [ht.1]
  have hint' : IntervalIntegrable f volume (sSup (Icc 0 x ∩ δ ⁻¹' Iic 0)) x :=
    hint.mono_set (by
      rw [uIcc_of_le hx'x, uIcc_of_le hε]; exact Icc_subset_Icc hx'0 hx.2)
  have hle := intervalIntegral.integral_mono_on_of_le_Ioo hx'x hint' intervalIntegrable_const
    (fun t ht => hf t ⟨hx'0.trans_lt ht.1, ht.2.trans_le hx.2⟩ (hpos' t ht))
  rw [intervalIntegral.integral_const, smul_eq_mul] at hle
  have hF := hFTC _ x hx'0 hx'x hx.2
  have k : (x - sSup (Icc 0 x ∩ δ ⁻¹' Iic 0)) * B ≤ ε * B :=
    mul_le_mul_of_nonneg_right (by linarith [hx.2]) hB
  linarith

/-- C4: two strictly decreasing solutions agree near `0`. -/
lemma uniq_local {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g1 g2 : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : ReinsPremium c cb) (hν : ClaimLaw ν) (hdens : SchmidliRuin.Exist.HasBoundedDensity ν)
    (hg1 : StrictAntiOn g1 (Ici 0)) (hs1 : SolvesEq5On c lam mu sigma cb ν g1 (Ici 0))
    (hg2 : StrictAntiOn g2 (Ici 0)) (hs2 : SolvesEq5On c lam mu sigma cb ν g2 (Ici 0)) :
    ∃ ε > 0, EqOn g1 g2 (Icc 0 ε) := by
  obtain ⟨τ1, hτ1, C1, hC1, h1⟩ :=
    inv_den_cmp hc hlam hmu hsigma hcb hν hdens hg1 hs1 hg2 hs2
  obtain ⟨τ2, hτ2, C2, hC2, h2⟩ :=
    inv_den_cmp hc hlam hmu hsigma hcb hν hdens hg2 hs2 hg1 hs1
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = min (min τ1 τ2) (1 / (2 * (C1 + C2))) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact lt_min (lt_min hτ1 hτ2) (by positivity)
  have hετ1 : ε ≤ τ1 := by rw [hεdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hετ2 : ε ≤ τ2 := by rw [hεdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hεC : ε * (C1 + C2) ≤ 1 / 2 := by
    have k : ε ≤ 1 / (2 * (C1 + C2)) := by rw [hεdef]; exact min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at k
    linarith
  set f1 : ℝ → ℝ := fun u => (den c lam cb ν g1 u)⁻¹ with hf1
  set f2 : ℝ → ℝ := fun u => (den c lam cb ν g2 u)⁻¹ with hf2
  have hi1 : ∀ a, 0 ≤ a → IntervalIntegrable f1 volume 0 a := fun a ha => (hs1 a ha).2.2.1
  have hi2 : ∀ a, 0 ≤ a → IntervalIntegrable f2 volume 0 a := fun a ha => (hs2 a ha).2.2.1
  set δ : ℝ → ℝ := fun z => (∫ u in (0:ℝ)..z, f1 u) - ∫ u in (0:ℝ)..z, f2 u with hδ
  have hδc : ContinuousOn δ (Icc 0 ε) := by
    have k1 := intervalIntegral.continuousOn_primitive_interval' (hi1 ε hε.le) left_mem_uIcc
    have k2 := intervalIntegral.continuousOn_primitive_interval' (hi2 ε hε.le) left_mem_uIcc
    rw [uIcc_of_le hε.le] at k1 k2
    exact k1.sub k2
  have hδ0 : δ 0 = 0 := by simp [hδ]
  have hFTC : ∀ a b, 0 ≤ a → a ≤ b → b ≤ ε → δ b - δ a = ∫ t in a..b, (f1 t - f2 t) := by
    intro a b ha hab _
    have hb : 0 ≤ b := ha.trans hab
    have e1 := intervalIntegral.integral_interval_sub_left (hi1 b hb) (hi1 a ha)
    have e2 := intervalIntegral.integral_interval_sub_left (hi2 b hb) (hi2 a ha)
    have j1 : IntervalIntegrable f1 volume a b :=
      (hi1 b hb).mono_set (by rw [uIcc_of_le hab, uIcc_of_le hb]; exact Icc_subset_Icc ha le_rfl)
    have j2 : IntervalIntegrable f2 volume a b :=
      (hi2 b hb).mono_set (by rw [uIcc_of_le hab, uIcc_of_le hb]; exact Icc_subset_Icc ha le_rfl)
    rw [intervalIntegral.integral_sub j1 j2]
    simp only [hδ]
    linarith
  have hint : IntervalIntegrable (fun t => f1 t - f2 t) volume 0 ε :=
    (hi1 ε hε.le).sub (hi2 ε hε.le)
  obtain ⟨xm, hxm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hε.le)
    (continuous_abs.comp_continuousOn hδc)
  have hM : ∀ z ∈ Icc (0:ℝ) ε, |δ z| ≤ |δ xm| := fun z hz => hmax hz
  have hM0 : 0 ≤ |δ xm| := abs_nonneg _
  have up := one_sided_bound (δ := δ) (f := fun t => f1 t - f2 t) (B := C1 * |δ xm|)
    (mul_nonneg hC1.le hM0) hδc hδ0 hint hFTC
    (fun t ht hpos => h1 t ⟨ht.1, ht.2.le.trans hετ1⟩ |δ xm|
      (fun z hz => hM z ⟨hz.1, hz.2.trans ht.2.le⟩) hpos.le)
  have hδc' : ContinuousOn (fun z => -δ z) (Icc 0 ε) := hδc.neg
  have dn := one_sided_bound (δ := fun z => -δ z) (f := fun t => f2 t - f1 t)
    (B := C2 * |δ xm|) (mul_nonneg hC2.le hM0) hδc' (by simp [hδ0]) (hint.neg.congr (by
      intro t _; simp only [Pi.neg_apply]; ring))
    (fun a b ha hab hbε => by
      have k := hFTC a b ha hab hbε
      have k2 : ∫ t in a..b, (f2 t - f1 t) = -∫ t in a..b, (f1 t - f2 t) := by
        rw [← intervalIntegral.integral_neg]; congr 1; ext t; ring
      rw [k2]; linarith)
    (fun t ht hpos => by
      have k := h2 t ⟨ht.1, ht.2.le.trans hετ2⟩ |δ xm|
        (fun z hz => by
          have := hM z ⟨hz.1, hz.2.trans ht.2.le⟩
          rw [abs_sub_comm]; exact this)
        (by simp only [hδ] at hpos; linarith)
      exact k)
  have habs : |δ xm| ≤ ε * (C1 + C2) * |δ xm| := by
    rw [abs_le']
    have a1 := up xm hxm
    have a2 := dn xm hxm
    have k1 : 0 ≤ ε * (C2 * |δ xm|) := mul_nonneg hε.le (mul_nonneg hC2.le hM0)
    have k2 : 0 ≤ ε * (C1 * |δ xm|) := mul_nonneg hε.le (mul_nonneg hC1.le hM0)
    constructor <;> nlinarith
  have hzero : |δ xm| = 0 := by
    have := mul_le_mul_of_nonneg_right hεC hM0
    nlinarith
  refine ⟨ε, hε, fun z hz => ?_⟩
  have hz0 : δ z = 0 := abs_eq_zero.1 (le_antisymm (hzero ▸ hM z hz) (abs_nonneg _))
  rw [g_eq_inv_yfun hs1 hz.1, g_eq_inv_yfun hs2 hz.1]
  unfold yfun
  simp only [hδ, f1, f2] at hz0
  rw [show (∫ x in (0:ℝ)..z, (den c lam cb ν g1 x)⁻¹) = ∫ x in (0:ℝ)..z, (den c lam cb ν g2 x)⁻¹ by
    linarith]


/-! ### C5: continuation of uniqueness, and the uniqueness half -/

lemma den_sub_le {c lam : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {g1 g2 : ℝ → ℝ} (hc : 0 < c) (hlam : 0 < lam) (hcb : ReinsPremium c cb) {t E : ℝ}
    (ht : 0 ≤ t)
    (hg10 : ∀ z ∈ Icc (0:ℝ) t, 0 ≤ g1 z) (hg1t : g1 t ≤ lam / c)
    (hg20 : ∀ z ∈ Icc (0:ℝ) t, 0 ≤ g2 z) (hg2t : g2 t ≤ lam / c)
    (h : ∀ b ∈ Icc (0:ℝ) 1, |phi c lam cb ν g1 t b - phi c lam cb ν g2 t b| ≤ E) :
    |den c lam cb ν g1 t - den c lam cb ν g2 t| ≤ E := by
  have up : den c lam cb ν g1 t - E ≤ den c lam cb ν g2 t := by
    rw [den_eq_sInf_phi c lam cb ν g2 t]
    refine le_csInf ((nonempty_Icc.2 zero_le_one).image _) ?_
    rintro _ ⟨b, hb, rfl⟩
    have k1 := den_le_phi (ν := ν) (g := g1) (cb := cb) hc hlam hcb ht hg10 hg1t hb
    have k2 := (abs_le.1 (h b hb)).2
    linarith
  have dn : den c lam cb ν g2 t - E ≤ den c lam cb ν g1 t := by
    rw [den_eq_sInf_phi c lam cb ν g1 t]
    refine le_csInf ((nonempty_Icc.2 zero_le_one).image _) ?_
    rintro _ ⟨b, hb, rfl⟩
    have k1 := den_le_phi (ν := ν) (g := g2) (cb := cb) hc hlam hcb ht hg20 hg2t hb
    have k2 := (abs_le.1 (h b hb)).1
    linarith
  rw [abs_le]; constructor <;> linarith

lemma den_lower_on {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : ReinsPremium c cb) (hν : ClaimLaw ν)
    (hg : StrictAntiOn g (Ici 0)) (hs : SolvesEq5On c lam mu sigma cb ν g (Ici 0))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ d > 0, ∀ t ∈ Icc a b, d ≤ den c lam cb ν g t := by
  have hcont := (den_continuousOn_sol hc hlam hcb hν hg hs).mono
    (fun t (ht : t ∈ Icc a b) => mem_Ioi.2 (lt_of_lt_of_le ha ht.1))
  obtain ⟨xm, hxm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hcont
  exact ⟨den c lam cb ν g xm, den_pos hc hlam hmu hsigma hcb hν hg hs (lt_of_lt_of_le ha hxm.1),
    fun t ht => hmin ht⟩

/-- Equal `g` on `[0, z]`-points give equal integrals `I`. -/
lemma I_eq_of_g_eq {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g1 g2 : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hg1 : StrictAntiOn g1 (Ici 0)) (hs1 : SolvesEq5On c lam mu sigma cb ν g1 (Ici 0))
    (hg2 : StrictAntiOn g2 (Ici 0)) (hs2 : SolvesEq5On c lam mu sigma cb ν g2 (Ici 0))
    {z : ℝ} (hz : 0 ≤ z) (h : g1 z = g2 z) :
    (∫ u in (0:ℝ)..z, (den c lam cb ν g1 u)⁻¹) = ∫ u in (0:ℝ)..z, (den c lam cb ν g2 u)⁻¹ := by
  have hb1 := sol_bounds hc hlam hg1 hs1 hz
  have hb2 := sol_bounds hc hlam hg2 hs2 hz
  have hY1 : yfun c lam mu sigma cb ν g1 z = 1 / g1 z := by
    rw [g_eq_inv_yfun hs1 hz, one_div_one_div]
  have hY2 : yfun c lam mu sigma cb ν g2 z = 1 / g2 z := by
    rw [g_eq_inv_yfun hs2 hz, one_div_one_div]
  have hY : yfun c lam mu sigma cb ν g1 z = yfun c lam mu sigma cb ν g2 z := by
    rw [hY1, hY2, h]
  unfold yfun at hY
  have hK : (mu ^ 2 / (2 * sigma ^ 2)) ≠ 0 := by positivity
  exact mul_left_cancel₀ hK (by linarith)

/-- C5: agreement on `[0, a]` (`a > 0`) extends to `[0, a + ε]`. -/
lemma uniq_step {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g1 g2 : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : ReinsPremium c cb) (hν : ClaimLaw ν)
    (hg1 : StrictAntiOn g1 (Ici 0)) (hs1 : SolvesEq5On c lam mu sigma cb ν g1 (Ici 0))
    (hg2 : StrictAntiOn g2 (Ici 0)) (hs2 : SolvesEq5On c lam mu sigma cb ν g2 (Ici 0))
    {a : ℝ} (ha : 0 < a) (heq : EqOn g1 g2 (Icc 0 a)) :
    ∃ ε > 0, EqOn g1 g2 (Icc 0 (a + ε)) := by
  have := hν.1
  obtain ⟨d1, hd1, hl1⟩ :=
    den_lower_on hc hlam hmu hsigma hcb hν hg1 hs1 ha (by linarith : a ≤ a + 1)
  obtain ⟨d2, hd2, hl2⟩ :=
    den_lower_on hc hlam hmu hsigma hcb hν hg2 hs2 ha (by linarith : a ≤ a + 1)
  have hKpos : 0 < mu ^ 2 / (2 * sigma ^ 2) := by positivity
  obtain ⟨L, hL⟩ : ∃ L, L = mu ^ 2 / (2 * sigma ^ 2) * (lam / c) ^ 2 := ⟨_, rfl⟩
  have hLpos : 0 < L := by rw [hL]; positivity
  have hcb0 : 0 ≤ cb 0 := cb_nonneg hcb ⟨le_rfl, zero_le_one⟩
  obtain ⟨E, hE⟩ : ∃ E, E = lam * L * (a + 1) + (c + cb 0) * L := ⟨_, rfl⟩
  have hEpos : 0 < E := by rw [hE]; positivity
  obtain ⟨C, hC⟩ : ∃ C, C = E / (d1 * d2) := ⟨_, rfl⟩
  have hCpos : 0 < C := by rw [hC]; positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = min 1 (1 / (2 * C)) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := by rw [hεdef]; exact min_le_left _ _
  have hεC : ε * C ≤ 1 / 2 := by
    have k : ε ≤ 1 / (2 * C) := by rw [hεdef]; exact min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at k
    linarith
  set f1 : ℝ → ℝ := fun u => (den c lam cb ν g1 u)⁻¹ with hf1
  set f2 : ℝ → ℝ := fun u => (den c lam cb ν g2 u)⁻¹ with hf2
  have hi1 : ∀ a, 0 ≤ a → IntervalIntegrable f1 volume 0 a := fun a ha => (hs1 a ha).2.2.1
  have hi2 : ∀ a, 0 ≤ a → IntervalIntegrable f2 volume 0 a := fun a ha => (hs2 a ha).2.2.1
  set δ : ℝ → ℝ := fun z => (∫ u in (0:ℝ)..z, f1 u) - ∫ u in (0:ℝ)..z, f2 u with hδ
  have hA : 0 ≤ a + ε := by linarith
  have hδc : ContinuousOn δ (Icc 0 (a + ε)) := by
    have k1 := intervalIntegral.continuousOn_primitive_interval' (hi1 (a + ε) hA) left_mem_uIcc
    have k2 := intervalIntegral.continuousOn_primitive_interval' (hi2 (a + ε) hA) left_mem_uIcc
    rw [uIcc_of_le hA] at k1 k2
    exact k1.sub k2
  have hδa : ∀ z ∈ Icc (0:ℝ) a, δ z = 0 := by
    intro z hz
    simp only [hδ, f1, f2]
    rw [I_eq_of_g_eq hc hlam hmu hsigma hg1 hs1 hg2 hs2 hz.1 (heq hz), sub_self]
  obtain ⟨xm, hxm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hA)
    (continuous_abs.comp_continuousOn hδc)
  have hM : ∀ z ∈ Icc (0:ℝ) (a + ε), |δ z| ≤ |δ xm| := fun z hz => hmax hz
  have hM0 : 0 ≤ |δ xm| := abs_nonneg _
  -- integrand bound on (a, a + ε]
  have hfb : ∀ t ∈ Ioc a (a + ε), |f1 t - f2 t| ≤ C * |δ xm| := by
    intro t ht
    have ht0 : 0 ≤ t := ha.le.trans ht.1.le
    have hta1 : t ∈ Icc a (a + 1) := ⟨ht.1.le, ht.2.trans (by linarith)⟩
    have hg10 : ∀ z ∈ Icc (0:ℝ) t, 0 ≤ g1 z := fun z hz => (sol_bounds hc hlam hg1 hs1 hz.1).2.1.le
    have hg20 : ∀ z ∈ Icc (0:ℝ) t, 0 ≤ g2 z := fun z hz => (sol_bounds hc hlam hg2 hs2 hz.1).2.1.le
    have hgd : ∀ z ∈ Icc (0:ℝ) t, |g1 z - g2 z| ≤ L * |δ xm| := by
      intro z hz
      have k := (g_diff hc hlam hmu hsigma hg1 hs1 hg2 hs2 hz.1).1
      rw [← hL] at k
      exact k.trans (mul_le_mul_of_nonneg_left (hM z ⟨hz.1, hz.2.trans ht.2⟩) hLpos.le)
    have hphi : ∀ b ∈ Icc (0:ℝ) 1,
        |phi c lam cb ν g1 t b - phi c lam cb ν g2 t b| ≤ E * |δ xm| := by
      intro b hb
      have hcv := conv_diff (ν := ν) (b := b) ht0 hb.1 (sol_continuousOn hc hlam hg1 hs1 ht0)
        (sol_continuousOn hc hlam hg2 hs2 ht0) hgd
      have hcbb : 0 ≤ cb b := cb_nonneg hcb hb
      have hcbb' : cb b ≤ cb 0 := hcb.1 ⟨le_rfl, zero_le_one⟩ hb hb.1
      have hcabs : |c - cb b| ≤ c + cb 0 := by rw [abs_le]; constructor <;> linarith
      have e : phi c lam cb ν g1 t b - phi c lam cb ν g2 t b =
          lam * (conv ν g1 t b - conv ν g2 t b) - (c - cb b) * (g1 t - g2 t) := by
        rw [phi_expand, phi_expand]; ring
      rw [e]
      have b1 : |lam * (conv ν g1 t b - conv ν g2 t b)| ≤ lam * L * (a + 1) * |δ xm| := by
        rw [abs_mul, abs_of_pos hlam]
        have k1 : L * |δ xm| * t ≤ L * |δ xm| * (a + 1) :=
          mul_le_mul_of_nonneg_left hta1.2 (mul_nonneg hLpos.le hM0)
        have k2 := mul_le_mul_of_nonneg_left (hcv.trans k1) hlam.le
        linarith
      have b2 : |(c - cb b) * (g1 t - g2 t)| ≤ (c + cb 0) * L * |δ xm| := by
        rw [abs_mul]
        have k := mul_le_mul hcabs (hgd t ⟨ht0, le_rfl⟩) (abs_nonneg _) (by linarith)
        linarith
      calc _ ≤ |lam * (conv ν g1 t b - conv ν g2 t b)| + |(c - cb b) * (g1 t - g2 t)| :=
            abs_sub _ _
        _ ≤ E * |δ xm| := by rw [hE]; linarith
    have hds := den_sub_le (ν := ν) hc hlam hcb ht0 hg10 (sol_bounds hc hlam hg1 hs1 ht0).2.2
      hg20 (sol_bounds hc hlam hg2 hs2 ht0).2.2 hphi
    have hp1 : 0 < den c lam cb ν g1 t := lt_of_lt_of_le hd1 (hl1 t hta1)
    have hp2 : 0 < den c lam cb ν g2 t := lt_of_lt_of_le hd2 (hl2 t hta1)
    have hprod : d1 * d2 ≤ den c lam cb ν g1 t * den c lam cb ν g2 t :=
      mul_le_mul (hl1 t hta1) (hl2 t hta1) hd2.le hp1.le
    simp only [hf1, hf2]
    rw [inv_sub_inv hp1.ne' hp2.ne', abs_div, abs_of_pos (mul_pos hp1 hp2), abs_sub_comm]
    calc |den c lam cb ν g1 t - den c lam cb ν g2 t| / (den c lam cb ν g1 t * den c lam cb ν g2 t)
        ≤ E * |δ xm| / (den c lam cb ν g1 t * den c lam cb ν g2 t) :=
          div_le_div_of_nonneg_right hds (mul_pos hp1 hp2).le
      _ ≤ E * |δ xm| / (d1 * d2) :=
          div_le_div_of_nonneg_left (mul_nonneg hEpos.le hM0) (mul_pos hd1 hd2) hprod
      _ = C * |δ xm| := by rw [hC]; ring
  have hxbound : ∀ x ∈ Icc a (a + ε), |δ x| ≤ ε * (C * |δ xm|) := by
    intro x hx
    have hx0 : 0 ≤ x := ha.le.trans hx.1
    have e1 := intervalIntegral.integral_interval_sub_left (hi1 x hx0) (hi1 a ha.le)
    have e2 := intervalIntegral.integral_interval_sub_left (hi2 x hx0) (hi2 a ha.le)
    have j1 : IntervalIntegrable f1 volume a x :=
      (hi1 x hx0).mono_set (by rw [uIcc_of_le hx.1, uIcc_of_le hx0]; exact Icc_subset_Icc ha.le le_rfl)
    have j2 : IntervalIntegrable f2 volume a x :=
      (hi2 x hx0).mono_set (by rw [uIcc_of_le hx.1, uIcc_of_le hx0]; exact Icc_subset_Icc ha.le le_rfl)
    have hδx : δ x = ∫ t in a..x, (f1 t - f2 t) := by
      rw [intervalIntegral.integral_sub j1 j2]
      have h0 := hδa a ⟨ha.le, le_rfl⟩
      simp only [hδ] at h0 ⊢
      linarith
    have key := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := x)
      (C := C * |δ xm|) (f := fun t => f1 t - f2 t) (fun t ht => by
        rw [uIoc_of_le hx.1] at ht
        rw [Real.norm_eq_abs]
        exact hfb t ⟨ht.1, ht.2.trans hx.2⟩)
    rw [Real.norm_eq_abs, ← hδx, abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - a)] at key
    have k : (C * |δ xm|) * (x - a) ≤ ε * (C * |δ xm|) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (by linarith [hx.2]) (mul_nonneg hCpos.le hM0)
    linarith
  have hzero : |δ xm| = 0 := by
    rcases le_or_gt xm a with h | h
    · rw [hδa xm ⟨hxm.1, h⟩, abs_zero]
    · have k := hxbound xm ⟨h.le, hxm.2⟩
      have k2 : ε * (C * |δ xm|) ≤ 1 / 2 * |δ xm| := by
        have := mul_le_mul_of_nonneg_right hεC hM0; linarith
      linarith
  refine ⟨ε, hε, fun z hz => ?_⟩
  have hz0 : δ z = 0 := abs_eq_zero.1 (le_antisymm (hzero ▸ hM z hz) (abs_nonneg _))
  rw [g_eq_inv_yfun hs1 hz.1, g_eq_inv_yfun hs2 hz.1]
  unfold yfun
  simp only [hδ, f1, f2] at hz0
  rw [show (∫ x in (0:ℝ)..z, (den c lam cb ν g1 x)⁻¹) = ∫ x in (0:ℝ)..z, (den c lam cb ν g2 x)⁻¹ by
    linarith]

/-- The uniqueness half of Theorem 2. -/
lemma uniqueness {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g1 g2 : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : ReinsPremium c cb) (hν : ClaimLaw ν) (hdens : SchmidliRuin.Exist.HasBoundedDensity ν)
    (hg1 : StrictAntiOn g1 (Ici 0)) (hs1 : SolvesEq5On c lam mu sigma cb ν g1 (Ici 0))
    (hg2 : StrictAntiOn g2 (Ici 0)) (hs2 : SolvesEq5On c lam mu sigma cb ν g2 (Ici 0)) :
    EqOn g1 g2 (Ici 0) := by
  obtain ⟨ε0, hε0, h0⟩ := uniq_local hc hlam hmu hsigma hcb hν hdens hg1 hs1 hg2 hs2
  by_contra hne
  have hB : ({x : ℝ | 0 ≤ x ∧ g1 x ≠ g2 x}).Nonempty := by
    simp only [EqOn, not_forall] at hne
    obtain ⟨x, hx, h⟩ := hne
    exact ⟨x, hx, h⟩
  have hBbdd : BddBelow {x : ℝ | 0 ≤ x ∧ g1 x ≠ g2 x} := ⟨0, fun x hx => hx.1⟩
  have hx0ε : ε0 ≤ sInf {x : ℝ | 0 ≤ x ∧ g1 x ≠ g2 x} := le_csInf hB (fun x hx => by
    by_contra hlt; push Not at hlt; exact hx.2 (h0 ⟨hx.1, hlt.le⟩))
  set x0 := sInf {x : ℝ | 0 ≤ x ∧ g1 x ≠ g2 x} with hx0def
  have hx0pos : 0 < x0 := lt_of_lt_of_le hε0 hx0ε
  have hlt : ∀ z, 0 ≤ z → z < x0 → g1 z = g2 z := fun z hz hzx => by
    by_contra hneq; exact notMem_of_lt_csInf hzx hBbdd ⟨hz, hneq⟩
  have hat : g1 x0 = g2 x0 := by
    by_contra hneq
    have hc1 := sol_continuousOn hc hlam hg1 hs1 hx0pos.le
    have hc2 := sol_continuousOn hc hlam hg2 hs2 hx0pos.le
    have hcw := (hc1.sub hc2) x0 ⟨hx0pos.le, le_rfl⟩
    have hd : 0 < |g1 x0 - g2 x0| := abs_pos.2 (sub_ne_zero.2 hneq)
    obtain ⟨η, hη, hηb⟩ := Metric.continuousWithinAt_iff.1 hcw _ hd
    have ht0 : 0 ≤ max 0 (x0 - η / 2) := le_max_left _ _
    have htx : max 0 (x0 - η / 2) < x0 := max_lt hx0pos (by linarith)
    have hdist : dist (max 0 (x0 - η / 2)) x0 < η := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · have := le_max_right 0 (x0 - η / 2); linarith
      · linarith
    have k := hηb ⟨ht0, htx.le⟩ hdist
    rw [Real.dist_eq] at k
    change |(g1 (max 0 (x0 - η / 2)) - g2 (max 0 (x0 - η / 2))) - (g1 x0 - g2 x0)|
      < |g1 x0 - g2 x0| at k
    rw [hlt _ ht0 htx, sub_self, zero_sub, abs_neg] at k
    exact lt_irrefl _ k
  have hEq : EqOn g1 g2 (Icc 0 x0) := fun z hz => by
    rcases eq_or_lt_of_le hz.2 with h | h
    · rw [h]; exact hat
    · exact hlt z hz.1 h
  obtain ⟨ε, hε, hstep⟩ := uniq_step hc hlam hmu hsigma hcb hν hg1 hs1 hg2 hs2 hx0pos hEq
  have hfin : x0 + ε ≤ x0 := le_csInf hB (fun x hx => by
    by_contra hlt'; push Not at hlt'
    exact hx.2 (hstep ⟨hx.1, hlt'.le⟩))
  linarith

/-! ## Existence, E2: continuation past a point where `den > 0` (Picard / Banach). -/

lemma den_congr {c lam : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g1 g2 : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (h : EqOn g1 g2 (Icc 0 x)) : den c lam cb ν g1 x = den c lam cb ν g2 x := by
  have hx' : g1 x = g2 x := h ⟨hx, le_rfl⟩
  have hI : ∀ b, (∫ z in (0:ℝ)..x, tail ν (x - z) b * g1 z)
      = ∫ z in (0:ℝ)..x, tail ν (x - z) b * g2 z := by
    intro b
    refine intervalIntegral.integral_congr (fun z hz => ?_)
    rw [uIcc_of_le hx] at hz
    simp only [h hz]
  unfold den
  simp only [hI, hx']

lemma inv_sub_inv_le {u v m : ℝ} (hm : 0 < m) (hu : m ≤ u) (hv : m ≤ v) :
    |1 / u - 1 / v| ≤ (1 / m) ^ 2 * |u - v| := by
  have hu0 : 0 < u := lt_of_lt_of_le hm hu
  have hv0 : 0 < v := lt_of_lt_of_le hm hv
  rw [div_sub_div _ _ hu0.ne' hv0.ne', abs_div, abs_of_pos (mul_pos hu0 hv0),
    div_le_iff₀ (mul_pos hu0 hv0)]
  have h1 : m * m ≤ u * v := mul_le_mul hu hv hm.le hu0.le
  have h2 : (1 / m) ^ 2 * (m * m) = 1 := by field_simp
  have h3 : 1 ≤ (1 / m) ^ 2 * (u * v) :=
    calc (1:ℝ) = (1 / m) ^ 2 * (m * m) := h2.symm
      _ ≤ (1 / m) ^ 2 * (u * v) := mul_le_mul_of_nonneg_left h1 (by positivity)
  calc |1 * v - u * 1| = 1 * |u - v| := by rw [one_mul, mul_one, abs_sub_comm, one_mul]
    _ ≤ ((1 / m) ^ 2 * (u * v)) * |u - v| := mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
    _ = (1 / m) ^ 2 * |u - v| * (u * v) := by ring

lemma phi_sub_le {c lam : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hlam : 0 < lam) (hcb : ReinsPremium c cb) {g1 g2 : ℝ → ℝ} {t B : ℝ} (ht : 0 ≤ t)
    (hc1 : ContinuousOn g1 (Icc 0 t)) (hc2 : ContinuousOn g2 (Icc 0 t))
    (hB : ∀ z ∈ Icc (0:ℝ) t, |g1 z - g2 z| ≤ B) {b : ℝ} (hb : b ∈ Icc (0:ℝ) 1) :
    |phi c lam cb ν g1 t b - phi c lam cb ν g2 t b| ≤ lam * (B * t) + (c + cb 0) * B := by
  have hconv := conv_diff (ν := ν) ht hb.1 hc1 hc2 hB
  have hcbb := cb_nonneg hcb hb
  have hcb0 := cb_nonneg hcb ⟨le_rfl, zero_le_one⟩
  have hcbl : cb b ≤ cb 0 := hcb.1 ⟨le_rfl, zero_le_one⟩ hb hb.1
  have hgt := hB t ⟨ht, le_rfl⟩
  have hc0 : 0 ≤ c := by
    obtain ⟨bl, -, hbl1, -, hle⟩ := hcb.2.2.2.2
    have := hle 1 ⟨hbl1, le_rfl⟩
    rw [hcb.2.2.1] at this; exact this
  rw [phi_expand, phi_expand]
  have e : lam * tail ν t b + lam * conv ν g1 t b - c * g1 t + cb b * g1 t -
      (lam * tail ν t b + lam * conv ν g2 t b - c * g2 t + cb b * g2 t)
      = lam * (conv ν g1 t b - conv ν g2 t b) + (cb b - c) * (g1 t - g2 t) := by ring
  rw [e]
  have h1 : |cb b - c| ≤ c + cb 0 := by rw [abs_le]; constructor <;> linarith
  calc |lam * (conv ν g1 t b - conv ν g2 t b) + (cb b - c) * (g1 t - g2 t)|
      ≤ |lam * (conv ν g1 t b - conv ν g2 t b)| + |(cb b - c) * (g1 t - g2 t)| := abs_add_le _ _
    _ ≤ lam * (B * t) + (c + cb 0) * B := by
      rw [abs_mul, abs_mul, abs_of_pos hlam]
      exact add_le_add (mul_le_mul_of_nonneg_left hconv hlam.le)
        (mul_le_mul h1 hgt (abs_nonneg _) (by linarith))

/-- Extension of `g0` past `a` by `1 / (Y0 + (J z - J a))`. -/
noncomputable def gext (g0 : ℝ → ℝ) (a Y0 : ℝ) (J : ℝ → ℝ) (z : ℝ) : ℝ :=
  if z ≤ a then g0 z else 1 / (Y0 + (J z - J a))

lemma gext_of_le {g0 : ℝ → ℝ} {a Y0 : ℝ} {J : ℝ → ℝ} {z : ℝ} (h : z ≤ a) :
    gext g0 a Y0 J z = g0 z := if_pos h

lemma gext_of_gt {g0 : ℝ → ℝ} {a Y0 : ℝ} {J : ℝ → ℝ} {z : ℝ} (h : a < z) :
    gext g0 a Y0 J z = 1 / (Y0 + (J z - J a)) := if_neg (not_le.2 h)

lemma gext_eqOn (g0 : ℝ → ℝ) (a Y0 : ℝ) (J : ℝ → ℝ) : EqOn (gext g0 a Y0 J) g0 (Iic a) :=
  fun _ hz => gext_of_le (mem_Iic.1 hz)

lemma gext_bounds {c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam) {g0 : ℝ → ℝ} {a Y0 : ℝ}
    {J : ℝ → ℝ} (hg0 : ∀ z ∈ Icc 0 a, 0 ≤ g0 z ∧ g0 z ≤ lam / c)
    (hJ : ∀ z, c / lam ≤ Y0 + (J z - J a)) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ gext g0 a Y0 J z ∧ gext g0 a Y0 J z ≤ lam / c := by
  rcases le_or_gt z a with h | h
  · rw [gext_of_le h]; exact hg0 z ⟨hz, h⟩
  · rw [gext_of_gt h]
    have hp : 0 < c / lam := div_pos hc hlam
    have h1 := hJ z
    refine ⟨one_div_nonneg.2 (by linarith), ?_⟩
    rw [← one_div_div c lam]
    exact one_div_le_one_div_of_le hp h1

lemma gext_continuousOn {g0 : ℝ → ℝ} {a Y0 : ℝ} {J : ℝ → ℝ} (ha : 0 ≤ a)
    (hg0c : ContinuousOn g0 (Icc 0 a)) (hga : g0 a = 1 / Y0) (hJc : Continuous J)
    (hJ : ∀ z, 0 < Y0 + (J z - J a)) : ContinuousOn (gext g0 a Y0 J) (Ici 0) := by
  have h1 : ContinuousOn (gext g0 a Y0 J) (Icc 0 a) :=
    hg0c.congr (fun z hz => gext_eqOn g0 a Y0 J (mem_Iic.2 hz.2))
  have h2 : ContinuousOn (gext g0 a Y0 J) (Ici a) := by
    have hc2 : Continuous (fun z => 1 / (Y0 + (J z - J a))) :=
      continuous_const.div (continuous_const.add (hJc.sub continuous_const))
        (fun z => (hJ z).ne')
    refine hc2.continuousOn.congr (fun z hz => ?_)
    rcases eq_or_lt_of_le (mem_Ici.1 hz) with h | h
    · rw [← h, gext_of_le le_rfl, hga]; simp only [sub_self, add_zero]
    · exact gext_of_gt h
  have := h1.union_of_isClosed h2 isClosed_Icc isClosed_Ici
  refine this.mono (fun z hz => ?_)
  rcases le_or_gt z a with h | h
  · exact Or.inl ⟨hz, h⟩
  · exact Or.inr h.le

lemma gext_sub {c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam) {g0 : ℝ → ℝ} {a Y0 : ℝ}
    {J1 J2 : ℝ → ℝ}
    (hJ1 : ∀ z, c / lam ≤ Y0 + (J1 z - J1 a)) (hJ2 : ∀ z, c / lam ≤ Y0 + (J2 z - J2 a))
    {D : ℝ} (hD : ∀ z, |(J1 z - J1 a) - (J2 z - J2 a)| ≤ D) (z : ℝ) :
    |gext g0 a Y0 J1 z - gext g0 a Y0 J2 z| ≤ (lam / c) ^ 2 * D := by
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD a)
  rcases le_or_gt z a with h | h
  · rw [gext_of_le h, gext_of_le h, sub_self, abs_zero]
    exact mul_nonneg (sq_nonneg _) hD0
  · rw [gext_of_gt h, gext_of_gt h]
    have := inv_sub_inv_le (div_pos hc hlam) (hJ1 z) (hJ2 z)
    rw [one_div_div] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    have e : Y0 + (J1 z - J1 a) - (Y0 + (J2 z - J2 a)) = (J1 z - J1 a) - (J2 z - J2 a) := by
      ring
    rw [e]; exact hD z

lemma den_gext_sub {c lam : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hc : 0 < c) (hlam : 0 < lam) (hcb : ReinsPremium c cb) {g0 : ℝ → ℝ} {a Y0 : ℝ}
    (ha : 0 ≤ a) (hg0c : ContinuousOn g0 (Icc 0 a)) (hga : g0 a = 1 / Y0)
    (hg0b : ∀ z ∈ Icc 0 a, 0 ≤ g0 z ∧ g0 z ≤ lam / c)
    {J1 J2 : ℝ → ℝ} (hJ1c : Continuous J1) (hJ2c : Continuous J2)
    (hJ1 : ∀ z, c / lam ≤ Y0 + (J1 z - J1 a)) (hJ2 : ∀ z, c / lam ≤ Y0 + (J2 z - J2 a))
    {D : ℝ} (hD : ∀ z, |(J1 z - J1 a) - (J2 z - J2 a)| ≤ D) {t : ℝ} (ht : 0 ≤ t) :
    |den c lam cb ν (gext g0 a Y0 J1) t - den c lam cb ν (gext g0 a Y0 J2) t|
      ≤ (lam / c) ^ 2 * D * (lam * t + c + cb 0) := by
  have hcl : 0 < c / lam := div_pos hc hlam
  have hp1 : ∀ z, 0 < Y0 + (J1 z - J1 a) := fun z => lt_of_lt_of_le hcl (hJ1 z)
  have hp2 : ∀ z, 0 < Y0 + (J2 z - J2 a) := fun z => lt_of_lt_of_le hcl (hJ2 z)
  have hc1 := (gext_continuousOn ha hg0c hga hJ1c hp1).mono (Icc_subset_Ici_self : Icc (0:ℝ) t ⊆ Ici 0)
  have hc2 := (gext_continuousOn ha hg0c hga hJ2c hp2).mono (Icc_subset_Ici_self : Icc (0:ℝ) t ⊆ Ici 0)
  have hb1 := fun z (hz : 0 ≤ z) => gext_bounds hc hlam hg0b hJ1 hz
  have hb2 := fun z (hz : 0 ≤ z) => gext_bounds hc hlam hg0b hJ2 hz
  refine den_sub_le hc hlam hcb ht (fun z hz => (hb1 z hz.1).1) (hb1 t ht).2
    (fun z hz => (hb2 z hz.1).1) (hb2 t ht).2 (fun b hb => ?_)
  have hB : ∀ z ∈ Icc (0:ℝ) t, |gext g0 a Y0 J1 z - gext g0 a Y0 J2 z| ≤ (lam / c) ^ 2 * D :=
    fun z _ => gext_sub hc hlam hJ1 hJ2 hD z
  have := phi_sub_le (ν := ν) hlam hcb ht hc1 hc2 hB hb
  calc _ ≤ _ := this
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- E2: a solution on `[0, a]` with `den(a) > 0` extends to a solution on `[0, a + η]`. -/
lemma extend_step {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : ReinsPremium c cb) (hν : ClaimLaw ν) {a : ℝ} (ha : 0 < a) {g0 : ℝ → ℝ}
    (hg0 : StrictAntiOn g0 (Icc 0 a)) (hs0 : SolvesEq5On c lam mu sigma cb ν g0 (Icc 0 a))
    (hg0c : ContinuousOn g0 (Icc 0 a)) (hg0b : ∀ z ∈ Icc 0 a, 0 ≤ g0 z ∧ g0 z ≤ lam / c)
    (hga_pos : 0 < g0 a) (hd0 : 0 < den c lam cb ν g0 a) :
    ∃ η > 0, ∃ g : ℝ → ℝ, StrictAntiOn g (Icc 0 (a + η)) ∧
      SolvesEq5On c lam mu sigma cb ν g (Icc 0 (a + η)) ∧ EqOn g g0 (Icc 0 a) := by
  haveI : IsProbabilityMeasure ν := hν.1
  have hcdf : Continuous (cdf ν) := hν.2.2
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = mu ^ 2 / (2 * sigma ^ 2) := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; positivity
  have hcl : 0 < c / lam := div_pos hc hlam
  have ha0 : (0:ℝ) ∈ Icc 0 a := ⟨le_rfl, ha.le⟩
  have haa : a ∈ Icc 0 a := ⟨ha.le, le_rfl⟩
  have hg00 : g0 0 = lam / c := by
    rw [(hs0 0 ha0).2.2.2, intervalIntegral.integral_same, mul_zero, zero_add, one_div_div]
  have hgal : g0 a < lam / c := hg00 ▸ hg0 ha0 haa ha
  obtain ⟨Y0, hY0d⟩ : ∃ Y0 : ℝ, Y0 = 1 / g0 a := ⟨_, rfl⟩
  have hga : g0 a = 1 / Y0 := by rw [hY0d, one_div_one_div]
  have hY0 : c / lam < Y0 := by
    have := one_div_lt_one_div_of_lt hga_pos hgal
    rwa [one_div_div, ← hY0d] at this
  have hY0pos : 0 < Y0 := hcl.trans hY0
  have hY0eq : Y0 = K * (∫ x in (0:ℝ)..a, (den c lam cb ν g0 x)⁻¹) + c / lam := by
    rw [hY0d, (hs0 a haa).2.2.2, one_div_one_div, hK]
  obtain ⟨d0, hd0e⟩ : ∃ d0 : ℝ, d0 = den c lam cb ν g0 a := ⟨_, rfl⟩
  rw [← hd0e] at hd0
  -- the reference extension `gh` (constant `g0 a` after `a`)
  have hJ0 : ∀ z, c / lam ≤ Y0 + ((fun _ : ℝ => (0:ℝ)) z - (fun _ : ℝ => (0:ℝ)) a) := fun z => by
    simp only [sub_self, add_zero]; exact hY0.le
  have hghc := gext_continuousOn ha.le hg0c hga continuous_const
    (fun z => lt_of_lt_of_le hcl (hJ0 z))
  have hghb := fun z (hz : 0 ≤ z) => gext_bounds hc hlam hg0b hJ0 hz
  have hdc : ContinuousOn (den c lam cb ν (gext g0 a Y0 (fun _ => 0))) (Ioi 0) :=
    den_continuousOn_of hc hlam hcb hcdf hghc (fun z hz => (hghb z hz).1)
      (fun z hz => (hghb z hz).2)
  have hdha : den c lam cb ν (gext g0 a Y0 (fun _ => 0)) a = d0 := by
    rw [hd0e]; exact den_congr ha.le (fun z hz => gext_eqOn g0 a Y0 _ (mem_Iic.2 hz.2))
  obtain ⟨δ, hδ, hδa⟩ := Metric.continuousAt_iff.1 ((hdc a ha).continuousAt (Ioi_mem_nhds ha))
    (d0 / 2) (by positivity)
  have hlow0 : ∀ t, a ≤ t → t < a + δ → d0 / 2 ≤ den c lam cb ν (gext g0 a Y0 (fun _ => 0)) t := by
    intro t h1 h2
    have hdist : dist t a < δ := by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
    have := hδa hdist
    rw [Real.dist_eq, hdha] at this
    linarith [(abs_lt.1 this).1]
  -- constants
  have hcb0 : 0 ≤ cb 0 := cb_nonneg hcb ⟨le_rfl, zero_le_one⟩
  obtain ⟨E, hEd⟩ : ∃ E : ℝ, E = (lam / c) ^ 2 * (lam * (a + 1) + c + cb 0) := ⟨_, rfl⟩
  have hEpos : 0 < E := by
    rw [hEd]
    have : 0 < lam * (a + 1) + c + cb 0 := by
      have := mul_pos hlam (by linarith : (0:ℝ) < a + 1); linarith
    positivity
  have hEt : ∀ D, 0 ≤ D → ∀ t, 0 ≤ t → t ≤ a + 1 →
      (lam / c) ^ 2 * D * (lam * t + c + cb 0) ≤ D * E := by
    intro D hD t ht0 ht1
    rw [hEd]
    have : lam * t + c + cb 0 ≤ lam * (a + 1) + c + cb 0 := by nlinarith
    have h2 : 0 ≤ (lam / c) ^ 2 * D := by positivity
    calc (lam / c) ^ 2 * D * (lam * t + c + cb 0)
        ≤ (lam / c) ^ 2 * D * (lam * (a + 1) + c + cb 0) := mul_le_mul_of_nonneg_left this h2
      _ = D * ((lam / c) ^ 2 * (lam * (a + 1) + c + cb 0)) := by ring
  obtain ⟨d, hdd⟩ : ∃ d : ℝ, d = d0 / 4 := ⟨_, rfl⟩
  have hd : 0 < d := by rw [hdd]; positivity
  obtain ⟨r, hr, hr1, hr2⟩ : ∃ r : ℝ, 0 < r ∧ 2 * r ≤ Y0 - c / lam ∧ 2 * r * E ≤ d0 / 4 := by
    refine ⟨min ((Y0 - c / lam) / 2) (d0 / (8 * E)), lt_min (by linarith) (by positivity),
      ?_, ?_⟩
    · have := min_le_left ((Y0 - c / lam) / 2) (d0 / (8 * E)); linarith
    · have h := min_le_right ((Y0 - c / lam) / 2) (d0 / (8 * E))
      have : 2 * min ((Y0 - c / lam) / 2) (d0 / (8 * E)) * E ≤ 2 * (d0 / (8 * E)) * E :=
        mul_le_mul_of_nonneg_right (by linarith) hEpos.le
      calc _ ≤ 2 * (d0 / (8 * E)) * E := this
        _ = d0 / 4 := by field_simp; ring
  have hA : 0 < K * (1 / d) := mul_pos hKpos (one_div_pos.2 hd)
  have hB : 0 < K * ((1 / d) ^ 2 * (2 * E)) := by positivity
  obtain ⟨η, hη, hηδ, hη1, hηs, hηc⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ δ / 2 ∧ η ≤ 1 ∧
      K * (1 / d) * η ≤ r ∧ K * ((1 / d) ^ 2 * (2 * E)) * η ≤ 1 / 2 := by
    refine ⟨min (min (δ / 2) 1) (min (r / (K * (1 / d))) ((1 / 2) / (K * ((1 / d) ^ 2 * (2 * E))))),
      lt_min (lt_min (by linarith) one_pos) (lt_min (div_pos hr hA) (div_pos (by norm_num) hB)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _), ?_, ?_⟩
    · have h := (min_le_right (min (δ / 2) 1) _).trans (min_le_left (r / (K * (1 / d)))
        ((1 / 2) / (K * ((1 / d) ^ 2 * (2 * E)))))
      calc K * (1 / d) * _ ≤ K * (1 / d) * (r / (K * (1 / d))) :=
            mul_le_mul_of_nonneg_left h hA.le
        _ = r := mul_div_cancel₀ r hA.ne'
    · have h := (min_le_right (min (δ / 2) 1) _).trans (min_le_right (r / (K * (1 / d)))
        ((1 / 2) / (K * ((1 / d) ^ 2 * (2 * E)))))
      calc K * ((1 / d) ^ 2 * (2 * E)) * _
          ≤ K * ((1 / d) ^ 2 * (2 * E)) * ((1 / 2) / (K * ((1 / d) ^ 2 * (2 * E)))) :=
            mul_le_mul_of_nonneg_left h hB.le
        _ = 1 / 2 := mul_div_cancel₀ _ hB.ne'
  have hle : a ≤ a + η := by linarith
  have hIcc_pos : ∀ t ∈ Icc a (a + η), 0 < t := fun t ht => lt_of_lt_of_le ha ht.1
  -- properties of the extension by `J` in the closed ball
  have hJabs : ∀ J : C(Icc a (a + η), ℝ), ∀ z, |IccExtend hle J z| ≤ ‖J‖ := by
    intro J z
    have := J.norm_coe_le_norm (projIcc a (a + η) hle z)
    rwa [Real.norm_eq_abs] at this
  have hJdiff : ∀ J1 J2 : C(Icc a (a + η), ℝ), ∀ z,
      |(IccExtend hle J1 z - IccExtend hle J1 a) - (IccExtend hle J2 z - IccExtend hle J2 a)|
        ≤ 2 * ‖J1 - J2‖ := by
    intro J1 J2 z
    have e : (IccExtend hle J1 z - IccExtend hle J1 a) - (IccExtend hle J2 z - IccExtend hle J2 a)
        = IccExtend hle (⇑(J1 - J2)) z - IccExtend hle (⇑(J1 - J2)) a := by
      simp only [IccExtend_apply, ContinuousMap.sub_apply]; ring
    rw [e]
    calc _ ≤ |IccExtend hle (⇑(J1 - J2)) z| + |IccExtend hle (⇑(J1 - J2)) a| := abs_sub _ _
      _ ≤ ‖J1 - J2‖ + ‖J1 - J2‖ := add_le_add (hJabs _ z) (hJabs _ a)
      _ = 2 * ‖J1 - J2‖ := by ring
  have key : ∀ J : C(Icc a (a + η), ℝ), ‖J‖ ≤ r →
      (∀ z, c / lam ≤ Y0 + (IccExtend hle J z - IccExtend hle J a)) ∧
      ContinuousOn (gext g0 a Y0 (IccExtend hle J)) (Ici 0) ∧
      ContinuousOn (den c lam cb ν (gext g0 a Y0 (IccExtend hle J))) (Ioi 0) ∧
      ∀ t ∈ Icc a (a + η), d ≤ den c lam cb ν (gext g0 a Y0 (IccExtend hle J)) t := by
    intro J hJ
    have hJb : ∀ z, c / lam ≤ Y0 + (IccExtend hle J z - IccExtend hle J a) := by
      intro z
      have h1 := hJabs J z
      have h2 := hJabs J a
      have : |IccExtend hle J z - IccExtend hle J a| ≤ 2 * r := by
        calc _ ≤ |IccExtend hle J z| + |IccExtend hle J a| := abs_sub _ _
          _ ≤ 2 * r := by linarith
      linarith [(abs_le.1 this).1]
    have hJc : Continuous (IccExtend hle J) := J.continuous.Icc_extend'
    have hgc := gext_continuousOn ha.le hg0c hga hJc (fun z => lt_of_lt_of_le hcl (hJb z))
    have hgb := fun z (hz : 0 ≤ z) => gext_bounds hc hlam hg0b hJb hz
    refine ⟨hJb, hgc, den_continuousOn_of hc hlam hcb hcdf hgc (fun z hz => (hgb z hz).1)
      (fun z hz => (hgb z hz).2), fun t ht => ?_⟩
    have hD : ∀ z, |(IccExtend hle J z - IccExtend hle J a)
        - ((fun _ : ℝ => (0:ℝ)) z - (fun _ : ℝ => (0:ℝ)) a)| ≤ 2 * r := by
      intro z
      simp only [sub_self, sub_zero]
      calc _ ≤ |IccExtend hle J z| + |IccExtend hle J a| := abs_sub _ _
        _ ≤ 2 * r := by linarith [hJabs J z, hJabs J a]
    have hdiff := den_gext_sub (ν := ν) hc hlam hcb ha.le hg0c hga hg0b hJc continuous_const
      hJb hJ0 hD (hIcc_pos t ht).le
    have h2 := hEt (2 * r) (by positivity) t (hIcc_pos t ht).le (by linarith [ht.2])
    have h3 := hlow0 t ht.1 (by linarith [ht.2])
    rw [hdd]
    linarith [(abs_le.1 hdiff).1]
  -- the Picard map on the closed ball
  have hT : ∀ J : Metric.closedBall (0 : C(Icc a (a + η), ℝ)) r,
      ∃ J' : Metric.closedBall (0 : C(Icc a (a + η), ℝ)) r, ∀ x : Icc a (a + η),
        J'.1 x = K * ∫ t in a..(x:ℝ),
          (den c lam cb ν (gext g0 a Y0 (IccExtend hle J.1)) t)⁻¹ := by
    intro J
    have hJr : ‖J.1‖ ≤ r := mem_closedBall_zero_iff.1 J.2
    obtain ⟨-, -, hdc', hlow'⟩ := key J.1 hJr
    have hfc : ContinuousOn (fun t => (den c lam cb ν (gext g0 a Y0 (IccExtend hle J.1)) t)⁻¹)
        (Icc a (a + η)) :=
      (hdc'.mono (fun t ht => mem_Ioi.2 (hIcc_pos t ht))).inv₀
        (fun t ht => (lt_of_lt_of_le hd (hlow' t ht)).ne')
    have hPc : ContinuousOn (fun x => K * ∫ t in a..x,
        (den c lam cb ν (gext g0 a Y0 (IccExtend hle J.1)) t)⁻¹) (Icc a (a + η)) := by
      have := intervalIntegral.continuousOn_primitive_interval' (μ := volume)
        (hfc.intervalIntegrable_of_Icc hle) (left_mem_uIcc (a := a) (b := a + η))
      rw [uIcc_of_le hle] at this
      exact continuousOn_const.mul this
    let J' : C(Icc a (a + η), ℝ) := ⟨fun x => K * ∫ t in a..(x:ℝ),
        (den c lam cb ν (gext g0 a Y0 (IccExtend hle J.1)) t)⁻¹,
      hPc.comp_continuous continuous_subtype_val (fun x => x.2)⟩
    have hJ'r : ‖J'‖ ≤ r := by
      refine (ContinuousMap.norm_le J' hr.le).2 (fun x => ?_)
      show ‖K * ∫ t in a..(x:ℝ), (den c lam cb ν (gext g0 a Y0 (IccExtend hle J.1)) t)⁻¹‖ ≤ r
      have hb : ‖∫ t in a..(x:ℝ), (den c lam cb ν (gext g0 a Y0 (IccExtend hle J.1)) t)⁻¹‖
          ≤ (1 / d) * |(x:ℝ) - a| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => ?_)
        rw [uIoc_of_le x.2.1] at ht
        have htI : t ∈ Icc a (a + η) := ⟨ht.1.le, ht.2.trans x.2.2⟩
        have hlo := hlow' t htI
        have hpos : 0 < den c lam cb ν (gext g0 a Y0 (IccExtend hle J.1)) t := hd.trans_le hlo
        rw [Real.norm_eq_abs, abs_inv, abs_of_pos hpos, one_div]
        exact (inv_le_inv₀ hpos hd).2 hlo
      have hxa : |(x:ℝ) - a| ≤ η := by
        rw [abs_of_nonneg (by linarith [x.2.1])]; linarith [x.2.2]
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos hKpos]
      calc K * ‖∫ t in a..(x:ℝ), (den c lam cb ν (gext g0 a Y0 (IccExtend hle J.1)) t)⁻¹‖
          ≤ K * ((1 / d) * |(x:ℝ) - a|) := mul_le_mul_of_nonneg_left hb hKpos.le
        _ ≤ K * ((1 / d) * η) := by gcongr
        _ = K * (1 / d) * η := by ring
        _ ≤ r := hηs
    exact ⟨⟨J', mem_closedBall_zero_iff.2 hJ'r⟩, fun x => rfl⟩
  choose T hTdef using hT
  -- contraction
  have hcontr : ∀ J1 J2 : Metric.closedBall (0 : C(Icc a (a + η), ℝ)) r,
      dist (T J1) (T J2) ≤ (1 / 2) * dist J1 J2 := by
    intro J1 J2
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have hJ1r : ‖J1.1‖ ≤ r := mem_closedBall_zero_iff.1 J1.2
    have hJ2r : ‖J2.1‖ ≤ r := mem_closedBall_zero_iff.1 J2.2
    obtain ⟨hb1, -, hdc1, hlow1⟩ := key J1.1 hJ1r
    obtain ⟨hb2, -, hdc2, hlow2⟩ := key J2.1 hJ2r
    have hfc1 : ContinuousOn (fun t => (den c lam cb ν (gext g0 a Y0 (IccExtend hle J1.1)) t)⁻¹)
        (Icc a (a + η)) :=
      (hdc1.mono (fun t ht => mem_Ioi.2 (hIcc_pos t ht))).inv₀
        (fun t ht => (lt_of_lt_of_le hd (hlow1 t ht)).ne')
    have hfc2 : ContinuousOn (fun t => (den c lam cb ν (gext g0 a Y0 (IccExtend hle J2.1)) t)⁻¹)
        (Icc a (a + η)) :=
      (hdc2.mono (fun t ht => mem_Ioi.2 (hIcc_pos t ht))).inv₀
        (fun t ht => (lt_of_lt_of_le hd (hlow2 t ht)).ne')
    have hN : 0 ≤ ‖J1.1 - J2.1‖ := norm_nonneg _
    refine (ContinuousMap.norm_le _ (by positivity)).2 (fun x => ?_)
    rw [ContinuousMap.sub_apply, hTdef J1 x, hTdef J2 x, ← mul_sub,
      ← intervalIntegral.integral_sub
        ((hfc1.mono (Icc_subset_Icc le_rfl x.2.2)).intervalIntegrable_of_Icc x.2.1)
        ((hfc2.mono (Icc_subset_Icc le_rfl x.2.2)).intervalIntegrable_of_Icc x.2.1)]
    have hb : ‖∫ t in a..(x:ℝ), ((den c lam cb ν (gext g0 a Y0 (IccExtend hle J1.1)) t)⁻¹
        - (den c lam cb ν (gext g0 a Y0 (IccExtend hle J2.1)) t)⁻¹)‖
        ≤ ((1 / d) ^ 2 * (2 * ‖J1.1 - J2.1‖ * E)) * |(x:ℝ) - a| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => ?_)
      rw [uIoc_of_le x.2.1] at ht
      have htI : t ∈ Icc a (a + η) := ⟨ht.1.le, ht.2.trans x.2.2⟩
      have hdiff := den_gext_sub (ν := ν) hc hlam hcb ha.le hg0c hga hg0b
        J1.1.continuous.Icc_extend' J2.1.continuous.Icc_extend' hb1 hb2
        (hJdiff J1.1 J2.1) (hIcc_pos t htI).le
      have h2 := hEt (2 * ‖J1.1 - J2.1‖) (by positivity) t (hIcc_pos t htI).le
        (by linarith [htI.2])
      have hinv := inv_sub_inv_le hd (hlow1 t htI) (hlow2 t htI)
      rw [one_div, one_div] at hinv
      rw [Real.norm_eq_abs]
      calc _ ≤ _ := hinv
        _ ≤ (1 / d) ^ 2 * (2 * ‖J1.1 - J2.1‖ * E) :=
          mul_le_mul_of_nonneg_left (hdiff.trans h2) (sq_nonneg _)
    have hxa : |(x:ℝ) - a| ≤ η := by
      rw [abs_of_nonneg (by linarith [x.2.1])]; linarith [x.2.2]
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos hKpos]
    calc K * ‖∫ t in a..(x:ℝ), ((den c lam cb ν (gext g0 a Y0 (IccExtend hle J1.1)) t)⁻¹
          - (den c lam cb ν (gext g0 a Y0 (IccExtend hle J2.1)) t)⁻¹)‖
        ≤ K * (((1 / d) ^ 2 * (2 * ‖J1.1 - J2.1‖ * E)) * |(x:ℝ) - a|) :=
          mul_le_mul_of_nonneg_left hb hKpos.le
      _ ≤ K * (((1 / d) ^ 2 * (2 * ‖J1.1 - J2.1‖ * E)) * η) := by gcongr
      _ = (K * ((1 / d) ^ 2 * (2 * E)) * η) * ‖J1.1 - J2.1‖ := by ring
      _ ≤ (1 / 2) * ‖J1.1 - J2.1‖ := mul_le_mul_of_nonneg_right hηc hN
  haveI : CompleteSpace (Metric.closedBall (0 : C(Icc a (a + η), ℝ)) r) :=
    Metric.isClosed_closedBall.completeSpace_coe
  haveI : Nonempty (Metric.closedBall (0 : C(Icc a (a + η), ℝ)) r) :=
    ⟨⟨0, Metric.mem_closedBall_self hr.le⟩⟩
  let Kc : NNReal := ⟨1 / 2, by norm_num⟩
  have hTc : ContractingWith Kc T :=
    ⟨by rw [← NNReal.coe_lt_coe]; show (1 / 2 : ℝ) < (1 : NNReal); norm_num,
      LipschitzWith.of_dist_le_mul (fun J1 J2 => hcontr J1 J2)⟩
  set Jst := ContractingWith.fixedPoint T hTc with hJst
  have hfix : T Jst = Jst := ContractingWith.fixedPoint_isFixedPt hTc
  have hJstr : ‖Jst.1‖ ≤ r := mem_closedBall_zero_iff.1 Jst.2
  obtain ⟨hbS, hgcS, hdcS, hlowS⟩ := key Jst.1 hJstr
  -- the solution
  obtain ⟨g, hgd⟩ : ∃ g, g = gext g0 a Y0 (IccExtend hle Jst.1) := ⟨_, rfl⟩
  rw [← hgd] at hgcS hdcS hlowS
  have hJx : ∀ x : Icc a (a + η), Jst.1 x = K * ∫ t in a..(x:ℝ), (den c lam cb ν g t)⁻¹ := by
    intro x
    have := hTdef Jst x
    rw [hfix, ← hgd] at this
    exact this
  have hJf : ∀ z ∈ Icc a (a + η),
      IccExtend hle Jst.1 z = K * ∫ t in a..z, (den c lam cb ν g t)⁻¹ := by
    intro z hz
    rw [IccExtend_of_mem hle _ hz]
    exact hJx ⟨z, hz⟩
  have hJfa : IccExtend hle Jst.1 a = 0 := by
    rw [hJf a ⟨le_rfl, hle⟩, intervalIntegral.integral_same, mul_zero]
  have hgz : ∀ z ∈ Icc a (a + η),
      g z = 1 / (Y0 + K * ∫ t in a..z, (den c lam cb ν g t)⁻¹) := by
    intro z hz
    rw [show g z = gext g0 a Y0 (IccExtend hle Jst.1) z by rw [hgd]]
    rcases eq_or_lt_of_le hz.1 with h | h
    · rw [← h, gext_of_le le_rfl, hga, intervalIntegral.integral_same, mul_zero, add_zero]
    · rw [gext_of_gt h, hJfa, sub_zero, hJf z hz]
  have hfpos : ∀ t ∈ Icc a (a + η), 0 < (den c lam cb ν g t)⁻¹ :=
    fun t ht => inv_pos.2 (hd.trans_le (hlowS t ht))
  have hfc : ContinuousOn (fun t => (den c lam cb ν g t)⁻¹) (Icc a (a + η)) :=
    (hdcS.mono (fun t ht => mem_Ioi.2 (hIcc_pos t ht))).inv₀
      (fun t ht => (lt_of_lt_of_le hd (hlowS t ht)).ne')
  have hF_strict : ∀ z w, a ≤ z → z < w → w ≤ a + η →
      (∫ t in a..z, (den c lam cb ν g t)⁻¹) < ∫ t in a..w, (den c lam cb ν g t)⁻¹ := by
    intro z w hz hzw hw
    have hi1 : IntervalIntegrable (fun t => (den c lam cb ν g t)⁻¹) volume a z :=
      (hfc.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc hz
    have hi2 : IntervalIntegrable (fun t => (den c lam cb ν g t)⁻¹) volume z w :=
      (hfc.mono (Icc_subset_Icc hz hw)).intervalIntegrable_of_Icc hzw.le
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have := intervalIntegral.intervalIntegral_pos_of_pos_on hi2
      (fun t ht => hfpos t ⟨by linarith [ht.1], by linarith [ht.2]⟩) hzw
    linarith
  have hF_nonneg : ∀ z ∈ Icc a (a + η), 0 ≤ ∫ t in a..z, (den c lam cb ν g t)⁻¹ :=
    fun z hz => intervalIntegral.integral_nonneg hz.1
      (fun t ht => (hfpos t ⟨ht.1, ht.2.trans hz.2⟩).le)
  have hg_on : ∀ z ∈ Icc a (a + η), ∀ w ∈ Icc a (a + η), z < w → g w < g z := by
    intro z hz w hw hzw
    rw [hgz z hz, hgz w hw]
    have h1 := hF_nonneg z hz
    have h2 := hF_strict z w hz.1 hzw hw.2
    apply one_div_lt_one_div_of_lt
    · have := mul_nonneg hKpos.le h1; linarith
    · have := mul_lt_mul_of_pos_left h2 hKpos; linarith
  have hgeq : EqOn g g0 (Icc 0 a) := fun z hz => by rw [hgd]; exact gext_of_le hz.2
  have hden_eq : ∀ x ∈ Icc 0 a, den c lam cb ν g x = den c lam cb ν g0 x :=
    fun x hx => den_congr hx.1 (fun z hz => hgeq ⟨hz.1, hz.2.trans hx.2⟩)
  have hii : ∀ u ∈ Icc 0 a,
      IntervalIntegrable (fun x => (den c lam cb ν g x)⁻¹) volume 0 u := by
    intro u hu
    have h := (hs0 u hu).2.2.1
    rw [intervalIntegrable_iff] at h ⊢
    refine h.congr_fun (fun x hx => ?_) measurableSet_uIoc
    rw [uIoc_of_le hu.1] at hx
    simp only [hden_eq x ⟨hx.1.le, hx.2.trans hu.2⟩]
  have hint_eq : ∀ u ∈ Icc 0 a,
      (∫ x in (0:ℝ)..u, (den c lam cb ν g x)⁻¹) = ∫ x in (0:ℝ)..u, (den c lam cb ν g0 x)⁻¹ := by
    intro u hu
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [uIcc_of_le hu.1] at hx
    simp only [hden_eq x ⟨hx.1, hx.2.trans hu.2⟩]
  refine ⟨η, hη, g, ?_, ?_, hgeq⟩
  · intro x hx y hy hxy
    rcases le_or_gt y a with hya | hya
    · rw [hgeq ⟨hx.1, hxy.le.trans hya⟩, hgeq ⟨hy.1, hya⟩]
      exact hg0 ⟨hx.1, hxy.le.trans hya⟩ ⟨hy.1, hya⟩ hxy
    · rcases le_or_gt x a with hxa | hxa
      · have h1 : g a ≤ g x := by
          rw [hgeq ⟨hx.1, hxa⟩, hgeq haa]
          exact hg0.antitoneOn ⟨hx.1, hxa⟩ haa hxa
        have h2 := hg_on a ⟨le_rfl, hle⟩ y ⟨hya.le, hy.2⟩ hya
        linarith
      · exact hg_on x ⟨hxa.le, hx.2⟩ y ⟨hya.le, hy.2⟩ hxy
  · intro u hu
    have hgi : IntervalIntegrable g volume 0 u :=
      (hgcS.mono (fun x hx => by
        rw [uIcc_of_le hu.1] at hx; exact mem_Ici.2 hx.1)).intervalIntegrable
    rcases le_or_gt u a with hua | hua
    · have hu' : u ∈ Icc 0 a := ⟨hu.1, hua⟩
      obtain ⟨-, h2, -, h4⟩ := hs0 u hu'
      refine ⟨hgi, fun x hx => ?_, hii u hu', ?_⟩
      · rw [hden_eq x ⟨hx.1.le, hx.2.le.trans hua⟩]; exact h2 x hx
      · rw [hgeq hu', h4, hint_eq u hu']
    · have hiau : IntervalIntegrable (fun x => (den c lam cb ν g x)⁻¹) volume a u :=
        (hfc.mono (Icc_subset_Icc le_rfl hu.2)).intervalIntegrable_of_Icc hua.le
      refine ⟨hgi, fun x hx => ?_, (hii a haa).trans hiau, ?_⟩
      · rcases lt_trichotomy x a with hxa | hxa | hxa
        · rw [hden_eq x ⟨hx.1.le, hxa.le⟩]; exact (hs0 a haa).2.1 x ⟨hx.1, hxa⟩
        · rw [hxa, hden_eq a haa, ← hd0e]; exact hd0.ne'
        · exact (hd.trans_le (hlowS x ⟨hxa.le, hx.2.le.trans hu.2⟩)).ne'
      · rw [hgz u ⟨hua.le, hu.2⟩,
          ← intervalIntegral.integral_add_adjacent_intervals (hii a haa) hiau,
          hint_eq a haa, hY0eq, ← hK]
        congr 1
        ring

/-- E1 brick (change of variables `x = X q`): if `X' = V`, `X` strictly increasing on `[0, σ]`,
`X 0 = 0` and `|V q| * F (X q) = 1` on `(0, σ]`, then `F` is integrable on `[0, X σ]` with
integral `σ`. -/
lemma integral_inv_cov {X V F : ℝ → ℝ} {σ : ℝ} (hσ : 0 ≤ σ) (hX0 : X 0 = 0)
    (hXd : ∀ q ∈ Icc 0 σ, HasDerivWithinAt X (V q) (Icc 0 σ) q)
    (hmono : StrictMonoOn X (Icc 0 σ))
    (hF : ∀ q ∈ Ioc 0 σ, |V q| * F (X q) = 1) :
    IntervalIntegrable F volume 0 (X σ) ∧ ∫ x in (0:ℝ)..X σ, F x = σ := by
  have hcont : ContinuousOn X (Icc 0 σ) := fun q hq => (hXd q hq).continuousWithinAt
  have h0 : (0:ℝ) ∈ Icc 0 σ := ⟨le_rfl, hσ⟩
  have hs : σ ∈ Icc 0 σ := ⟨hσ, le_rfl⟩
  have hXσ : 0 ≤ X σ := by
    rcases eq_or_lt_of_le hσ with h | h
    · rw [← h, hX0]
    · rw [← hX0]; exact (hmono h0 hs h).le
  have himg : X '' Icc 0 σ = Icc 0 (X σ) := by
    apply Subset.antisymm
    · rintro _ ⟨q, hq, rfl⟩
      rw [← hX0]
      exact ⟨hmono.monotoneOn h0 hq hq.1, hmono.monotoneOn hq hs hq.2⟩
    · have := hcont.surjOn_Icc h0 hs
      rwa [hX0] at this
  have heq : EqOn (fun q => |V q| • F (X q)) (fun _ => (1:ℝ)) (Ioc 0 σ) := fun q hq => by
    simp only [smul_eq_mul]; exact hF q hq
  have hint1 : IntegrableOn (fun q => |V q| • F (X q)) (Icc 0 σ) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact ((continuous_const (y := (1:ℝ))).integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr_fun
      heq.symm measurableSet_Ioc
  have hInj := hmono.injOn
  have hI := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hXd hInj F
  have hII := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc hXd hInj
    F).2 hint1
  rw [himg] at hI hII
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hXσ]; exact hII
  · rw [intervalIntegral.integral_of_le hXσ, ← integral_Icc_eq_integral_Ioc, hI,
      integral_Icc_eq_integral_Ioc, setIntegral_congr_fun measurableSet_Ioc heq]
    simp [hσ]

/-- With a density bounded by `P`, the cdf is `P`-Lipschitz. -/
lemma cdf_sub_le {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {p : ℝ → ℝ} {P : ℝ} (hp : ∀ x, 0 ≤ p x ∧ p x ≤ P)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (p x))) {y' y : ℝ} (hy : y' ≤ y) :
    cdf ν y - cdf ν y' ≤ P * (y - y') := by
  have hP : 0 ≤ P := le_trans (hp 0).1 (hp 0).2
  have h1 : ν (Iic y) = ν (Iic y') + ν (Ioc y' y) := by
    rw [← Iic_union_Ioc_eq_Iic hy]
    exact measure_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
  have h2 : ν (Ioc y' y) ≤ ENNReal.ofReal (P * (y - y')) := by
    rw [hν, withDensity_apply _ measurableSet_Ioc]
    calc ∫⁻ x in Ioc y' y, ENNReal.ofReal (p x) ≤ ∫⁻ x in Ioc y' y, ENNReal.ofReal P :=
          lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hp x).2)
      _ = ENNReal.ofReal P * volume (Ioc y' y) := setLIntegral_const _ _
      _ = ENNReal.ofReal (P * (y - y')) := by rw [Real.volume_Ioc, ENNReal.ofReal_mul hP]
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def, h1,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
  rw [ENNReal.toReal_ofReal (mul_nonneg hP (by linarith))] at h3
  linarith

/-- For `b ≥ b̲ > 0` the tail `1 - G(x/b)` is `P/b̲`-Lipschitz in `x`. -/
lemma tail_lip {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {p : ℝ → ℝ} {P : ℝ} (hp : ∀ x, 0 ≤ p x ∧ p x ≤ P)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (p x))) {bl b : ℝ} (hbl : 0 < bl)
    (hb : bl ≤ b) (x x' : ℝ) : |tail ν x b - tail ν x' b| ≤ P / bl * |x - x'| := by
  have hb0 : 0 < b := hbl.trans_le hb
  have hP : 0 ≤ P := le_trans (hp 0).1 (hp 0).2
  unfold tail
  rw [if_neg hb0.ne', if_neg hb0.ne']
  have key : ∀ u v : ℝ, v ≤ u → cdf ν (u / b) - cdf ν (v / b) ≤ P / bl * |u - v| := by
    intro u v huv
    have h := cdf_sub_le hp hν (div_le_div_of_nonneg_right huv hb0.le)
    have e : P * (u / b - v / b) = P / b * (u - v) := by ring
    rw [e] at h
    rw [abs_of_nonneg (by linarith)]
    calc _ ≤ P / b * (u - v) := h
      _ ≤ P / bl * (u - v) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hP hbl hb) (by linarith)
  rcases le_total x' x with h | h
  · have m : cdf ν (x' / b) ≤ cdf ν (x / b) := (cdf ν).mono (div_le_div_of_nonneg_right h hb0.le)
    rw [show (1 - cdf ν (x / b)) - (1 - cdf ν (x' / b)) = -(cdf ν (x / b) - cdf ν (x' / b)) by ring,
      abs_neg, abs_of_nonneg (by linarith)]
    exact key x x' h
  · have m : cdf ν (x / b) ≤ cdf ν (x' / b) := (cdf ν).mono (div_le_div_of_nonneg_right h hb0.le)
    rw [show (1 - cdf ν (x / b)) - (1 - cdf ν (x' / b)) = cdf ν (x' / b) - cdf ν (x / b) by ring,
      abs_of_nonneg (by linarith), abs_sub_comm]
    exact key x' x h

/-! ## E1 (s-variable) objects: `g̃(q) = 1/(Kq + c/λ)`, `X = ∫ W`, bracket `PhiS`. -/

noncomputable def gt (K c lam q : ℝ) : ℝ := 1 / (K * q + c / lam)

noncomputable def Xof (W : ℝ → ℝ) (s : ℝ) : ℝ := ∫ q in (0:ℝ)..s, W q

noncomputable def PhiS (c lam K : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (W : ℝ → ℝ) (s b : ℝ) : ℝ :=
  lam * tail ν (Xof W s) b
    + lam * (∫ q in (0:ℝ)..s, tail ν (Xof W s - Xof W q) b * gt K c lam q * W q)
    - (c - cb b) * gt K c lam s

lemma tail_continuous {ν : Measure ℝ} (hcdf : Continuous (cdf ν)) {b : ℝ} (hb : b ≠ 0) :
    Continuous (fun x => tail ν x b) := by
  unfold tail
  simp only [if_neg hb]
  exact continuous_const.sub (hcdf.comp (continuous_id.div_const b))

lemma Xof_continuous {W : ℝ → ℝ} (hW : Continuous W) : Continuous (Xof W) := by
  unfold Xof
  exact intervalIntegral.continuous_primitive (fun a b => hW.intervalIntegrable a b) 0

lemma gt_bounds {K c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hK : 0 ≤ K) {q : ℝ} (hq : 0 ≤ q) :
    0 < gt K c lam q ∧ gt K c lam q ≤ lam / c := by
  have h1 : c / lam ≤ K * q + c / lam := by have := mul_nonneg hK hq; linarith
  have h0 : 0 < c / lam := div_pos hc hlam
  unfold gt
  refine ⟨one_div_pos.2 (h0.trans_le h1), ?_⟩
  rw [← one_div_div c lam]
  exact one_div_le_one_div_of_le h0 h1

lemma gt_continuousOn {K c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hK : 0 ≤ K) :
    ContinuousOn (gt K c lam) (Ici 0) := by
  have h0 : 0 < c / lam := div_pos hc hlam
  unfold gt
  refine continuousOn_const.div ((continuous_const.mul continuous_id).add
    continuous_const).continuousOn (fun q hq => ?_)
  have := mul_nonneg hK (mem_Ici.1 hq)
  exact ne_of_gt (by linarith)

lemma Xof_sub_le {W1 W2 : ℝ → ℝ} (hW1 : Continuous W1) (hW2 : Continuous W2) {s δ : ℝ}
    (hs : 0 ≤ s) (hδ : ∀ q ∈ Icc 0 s, |W1 q - W2 q| ≤ δ) :
    ∀ q ∈ Icc 0 s, |Xof W1 q - Xof W2 q| ≤ δ * s := by
  intro q hq
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hδ 0 ⟨le_rfl, hs⟩)
  unfold Xof
  rw [← intervalIntegral.integral_sub (hW1.intervalIntegrable _ _) (hW2.intervalIntegrable _ _)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := q) (C := δ)
    (f := fun x => W1 x - W2 x) (fun x hx => by
      rw [uIoc_of_le hq.1] at hx
      rw [Real.norm_eq_abs]; exact hδ x ⟨hx.1.le, hx.2.trans hq.2⟩)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hq.1] at this
  exact this.trans (mul_le_mul_of_nonneg_left hq.2 hδ0)

/-- Lipschitz dependence of the s-variable bracket on `W` (sup norm), uniformly in `b ≥ b̲`. -/
lemma PhiS_sub_le {c lam K : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hc : 0 < c) (hlam : 0 < lam) (hK : 0 ≤ K) (hcdf : Continuous (cdf ν))
    {P bl b : ℝ} (hbl : 0 < bl) (hb : bl ≤ b) (hP : 0 ≤ P)
    (hT : ∀ x x' : ℝ, |tail ν x b - tail ν x' b| ≤ P / bl * |x - x'|)
    {W1 W2 : ℝ → ℝ} (hW1 : Continuous W1) (hW2 : Continuous W2) {s M δ : ℝ} (hs : 0 ≤ s)
    (hM : ∀ q ∈ Icc 0 s, |W1 q| ≤ M) (hδ : ∀ q ∈ Icc 0 s, |W1 q - W2 q| ≤ δ) :
    |PhiS c lam K cb ν W1 s b - PhiS c lam K cb ν W2 s b|
      ≤ lam * (P / bl * (δ * s))
        + lam * ((P / bl * (2 * (δ * s)) * (lam / c) * M + (lam / c) * δ) * s) := by
  have hb0 : b ≠ 0 := (hbl.trans_le hb).ne'
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 ⟨le_rfl, hs⟩)
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hδ 0 ⟨le_rfl, hs⟩)
  have hPb : 0 ≤ P / bl := div_nonneg hP hbl.le
  have hX := Xof_sub_le hW1 hW2 hs hδ
  have hTc := tail_continuous hcdf hb0
  have hgc := (gt_continuousOn hc hlam hK (K := K)).mono
    (fun q (hq : q ∈ uIcc 0 s) => by rw [uIcc_of_le hs] at hq; exact mem_Ici.2 hq.1)
  have hi : ∀ W : ℝ → ℝ, Continuous W → IntervalIntegrable
      (fun q => tail ν (Xof W s - Xof W q) b * gt K c lam q * W q) volume 0 s := by
    intro W hW
    refine ContinuousOn.intervalIntegrable ?_
    exact ((hTc.comp (continuous_const.sub (Xof_continuous hW))).continuousOn.mul hgc).mul
      hW.continuousOn
  have hint : |(∫ q in (0:ℝ)..s, tail ν (Xof W1 s - Xof W1 q) b * gt K c lam q * W1 q)
      - ∫ q in (0:ℝ)..s, tail ν (Xof W2 s - Xof W2 q) b * gt K c lam q * W2 q|
      ≤ (P / bl * (2 * (δ * s)) * (lam / c) * M + (lam / c) * δ) * s := by
    rw [← intervalIntegral.integral_sub (hi W1 hW1) (hi W2 hW2)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := s)
      (C := P / bl * (2 * (δ * s)) * (lam / c) * M + (lam / c) * δ)
      (f := fun q => tail ν (Xof W1 s - Xof W1 q) b * gt K c lam q * W1 q
        - tail ν (Xof W2 s - Xof W2 q) b * gt K c lam q * W2 q) (fun q hq => by
        rw [uIoc_of_le hs] at hq
        have hqI : q ∈ Icc 0 s := ⟨hq.1.le, hq.2⟩
        have hg := gt_bounds hc hlam hK hq.1.le (K := K)
        have hT1 : |tail ν (Xof W1 s - Xof W1 q) b - tail ν (Xof W2 s - Xof W2 q) b|
            ≤ P / bl * (2 * (δ * s)) := by
          refine (hT _ _).trans (mul_le_mul_of_nonneg_left ?_ hPb)
          have e : Xof W1 s - Xof W1 q - (Xof W2 s - Xof W2 q)
              = (Xof W1 s - Xof W2 s) - (Xof W1 q - Xof W2 q) := by ring
          rw [e]
          calc _ ≤ |Xof W1 s - Xof W2 s| + |Xof W1 q - Xof W2 q| := abs_sub _ _
            _ ≤ δ * s + δ * s := add_le_add (hX s ⟨hs, le_rfl⟩) (hX q hqI)
            _ = 2 * (δ * s) := by ring
        have e : tail ν (Xof W1 s - Xof W1 q) b * gt K c lam q * W1 q
            - tail ν (Xof W2 s - Xof W2 q) b * gt K c lam q * W2 q
            = (tail ν (Xof W1 s - Xof W1 q) b - tail ν (Xof W2 s - Xof W2 q) b)
                * gt K c lam q * W1 q
              + tail ν (Xof W2 s - Xof W2 q) b * gt K c lam q * (W1 q - W2 q) := by ring
        rw [Real.norm_eq_abs, e]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_mul, abs_of_pos hg.1]
          exact mul_le_mul (mul_le_mul hT1 hg.2 hg.1.le (by positivity)) (hM q hqI)
            (abs_nonneg _) (by positivity)
        · rw [abs_mul, abs_mul, abs_of_pos hg.1, abs_of_nonneg (tail_nonneg ν _ _)]
          calc tail ν (Xof W2 s - Xof W2 q) b * gt K c lam q * |W1 q - W2 q|
              ≤ 1 * (lam / c) * δ :=
                mul_le_mul (mul_le_mul (tail_le_one ν _ _) hg.2 hg.1.le zero_le_one)
                  (hδ q hqI) (abs_nonneg _) (by positivity)
            _ = lam / c * δ := by ring)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs] at this
    exact this
  have htail : |tail ν (Xof W1 s) b - tail ν (Xof W2 s) b| ≤ P / bl * (δ * s) :=
    (hT _ _).trans (mul_le_mul_of_nonneg_left (hX s ⟨hs, le_rfl⟩) hPb)
  unfold PhiS
  have e : lam * tail ν (Xof W1 s) b
      + lam * (∫ q in (0:ℝ)..s, tail ν (Xof W1 s - Xof W1 q) b * gt K c lam q * W1 q)
      - (c - cb b) * gt K c lam s
      - (lam * tail ν (Xof W2 s) b
      + lam * (∫ q in (0:ℝ)..s, tail ν (Xof W2 s - Xof W2 q) b * gt K c lam q * W2 q)
      - (c - cb b) * gt K c lam s)
      = lam * (tail ν (Xof W1 s) b - tail ν (Xof W2 s) b)
        + lam * ((∫ q in (0:ℝ)..s, tail ν (Xof W1 s - Xof W1 q) b * gt K c lam q * W1 q)
          - ∫ q in (0:ℝ)..s, tail ν (Xof W2 s - Xof W2 q) b * gt K c lam q * W2 q) := by ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos hlam]; exact mul_le_mul_of_nonneg_left htail hlam.le
  · rw [abs_mul, abs_of_pos hlam]; exact mul_le_mul_of_nonneg_left hint hlam.le

/-! ## E1 fixed point (session 4): generic infimum comparison, bracket bounds, `DS`. -/

lemma ev_small (A r : ℝ) (hr : 0 < r) : ∀ᶠ s in 𝓝[>] (0:ℝ), A * s < r := by
  have h := (continuous_const_mul A).tendsto (0:ℝ)
  rw [mul_zero] at h
  exact (h.mono_left nhdsWithin_le_nhds).eventually (eventually_lt_nhds hr)

lemma sInf_ge_sub {f1 f2 : ℝ → ℝ} {bl ε : ℝ} (hbl0 : 0 ≤ bl) (hbl1 : bl ≤ 1)
    (hB2 : BddBelow (f2 '' Icc 0 1)) (h1 : ∀ b ∈ Ico 0 bl, f1 1 ≤ f1 b)
    (hd : ∀ b ∈ Icc bl 1, |f1 b - f2 b| ≤ ε) :
    sInf (f2 '' Icc 0 1) - ε ≤ sInf (f1 '' Icc 0 1) := by
  have key : ∀ b ∈ Icc bl 1, sInf (f2 '' Icc 0 1) - ε ≤ f1 b := by
    intro b hb
    have h2 : sInf (f2 '' Icc 0 1) ≤ f2 b := csInf_le hB2 ⟨b, ⟨hbl0.trans hb.1, hb.2⟩, rfl⟩
    have := (abs_le.1 (hd b hb)).1
    linarith
  refine le_csInf ((nonempty_Icc.2 zero_le_one).image _) ?_
  rintro _ ⟨b, hb, rfl⟩
  rcases lt_or_ge b bl with h | h
  · exact (key 1 ⟨hbl1, le_rfl⟩).trans (h1 b ⟨hb.1, h⟩)
  · exact key b ⟨h, hb.2⟩

lemma sInf_sub_abs_le {f1 f2 : ℝ → ℝ} {bl ε : ℝ} (hbl0 : 0 ≤ bl) (hbl1 : bl ≤ 1)
    (hB1 : BddBelow (f1 '' Icc 0 1)) (hB2 : BddBelow (f2 '' Icc 0 1))
    (h1 : ∀ b ∈ Ico 0 bl, f1 1 ≤ f1 b) (h2 : ∀ b ∈ Ico 0 bl, f2 1 ≤ f2 b)
    (hd : ∀ b ∈ Icc bl 1, |f1 b - f2 b| ≤ ε) :
    |sInf (f1 '' Icc 0 1) - sInf (f2 '' Icc 0 1)| ≤ ε := by
  have a1 := sInf_ge_sub hbl0 hbl1 hB2 h1 hd
  have a2 := sInf_ge_sub (f1 := f2) (f2 := f1) hbl0 hbl1 hB1 h2
    (fun b hb => by rw [abs_sub_comm]; exact hd b hb)
  rw [abs_le]; constructor <;> linarith

lemma bracket_ge_high {c lam : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hlam : 0 < lam) (hcb : ReinsPremium c cb) {P bl : ℝ} (hbl : 0 < bl) (hbl1 : bl ≤ 1)
    (hblc : ∀ b ∈ Ico 0 bl, c < cb b) (hG : ∀ s, 0 ≤ s → cdf ν s ≤ P * s)
    {x I G : ℝ} (hx : 0 ≤ x) (hxs : 2 * P * x ≤ bl / 2) (hI : 0 ≤ I) (hG0 : 0 ≤ G)
    {b : ℝ} (hb : b ∈ Ico 0 bl) :
    min (lam / 2) ((cb (bl / 2) - c) * G) ≤ lam * tail ν x b + lam * I - (c - cb b) * G := by
  have h5 := mul_nonneg hlam.le hI
  have htl := tail_nonneg ν x b
  rcases lt_or_ge b (bl / 2) with hb2 | hb2
  · have hanti : cb (bl / 2) ≤ cb b :=
      hcb.1 ⟨hb.1, by linarith [hb.2]⟩ ⟨by linarith, by linarith⟩ hb2.le
    have k1 : (cb (bl / 2) - c) * G ≤ (cb b - c) * G :=
      mul_le_mul_of_nonneg_right (by linarith) hG0
    have k2 := mul_nonneg hlam.le htl
    refine (min_le_right _ _).trans ?_
    nlinarith
  · have hbpos : 0 < b := by linarith
    have htail : tail ν x b = 1 - cdf ν (x / b) := by simp [tail, hbpos.ne']
    have h1 : cdf ν (x / b) ≤ 1 / 2 := by
      have k := hG (x / b) (div_nonneg hx hbpos.le)
      have k' : P * (x / b) ≤ 1 / 2 := by
        rw [mul_div_assoc', div_le_iff₀ hbpos]
        nlinarith
      linarith
    have hcbb : c < cb b := hblc b hb
    have k3 : 0 ≤ (cb b - c) * G := mul_nonneg (by linarith) hG0
    rw [htail]
    refine (min_le_left _ _).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left h1 hlam.le]

lemma bracket_ge_low {c lam : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hlam : 0 < lam) (hcb : ReinsPremium c cb) {P bl : ℝ} (hP : 0 ≤ P) (hbl : 0 < bl)
    (hG : ∀ s, 0 ≤ s → cdf ν s ≤ P * s) {x I G : ℝ} (hx : 0 ≤ x) (hI : 0 ≤ I) (hG0 : 0 ≤ G)
    {b : ℝ} (hb : b ∈ Icc bl 1) :
    (lam - c * G) - lam * P * x / bl ≤ lam * tail ν x b + lam * I - (c - cb b) * G := by
  have hbpos : 0 < b := lt_of_lt_of_le hbl hb.1
  have htail : tail ν x b = 1 - cdf ν (x / b) := by simp [tail, hbpos.ne']
  have h1 : cdf ν (x / b) ≤ P * x / bl := by
    calc cdf ν (x / b) ≤ P * (x / b) := hG (x / b) (div_nonneg hx hbpos.le)
      _ ≤ P * (x / bl) := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hx hbl hb.1) hP
      _ = P * x / bl := by ring
  have h3 : 0 ≤ cb b * G := mul_nonneg (cb_nonneg hcb ⟨hbpos.le, hb.2⟩) hG0
  have h4 := mul_le_mul_of_nonneg_left h1 hlam.le
  have h5 := mul_nonneg hlam.le hI
  rw [htail]
  have h6 : lam * (P * x / bl) = lam * P * x / bl := by ring
  nlinarith

lemma lam_sub_cgt {K c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hK : 0 ≤ K) {s : ℝ}
    (hs : 0 ≤ s) : lam - c * gt K c lam s = lam * K * s / (K * s + c / lam) := by
  have hD : 0 < K * s + c / lam := by
    have := mul_nonneg hK hs; have := div_pos hc hlam; linarith
  have e : lam * (c / lam) = c := mul_div_cancel₀ c hlam.ne'
  unfold gt
  rw [eq_div_iff hD.ne', sub_mul, one_div, mul_assoc, inv_mul_cancel₀ hD.ne', mul_one, mul_add, e]
  ring

lemma lam_sub_cgt_le {K c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hK : 0 ≤ K) {s : ℝ}
    (hs : 0 ≤ s) : lam - c * gt K c lam s ≤ lam * K * (lam / c) * s := by
  rw [lam_sub_cgt hc hlam hK hs]
  have hcl : 0 < c / lam := div_pos hc hlam
  have hKs := mul_nonneg hK hs
  calc lam * K * s / (K * s + c / lam) ≤ lam * K * s / (c / lam) :=
        div_le_div_of_nonneg_left (by positivity) hcl (by linarith)
    _ = lam * K * (lam / c) * s := by field_simp

lemma lam_sub_cgt_ge {K c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hK : 0 ≤ K) {s : ℝ}
    (hs : 0 ≤ s) (h : lam * K * s ≤ c) : lam * K * (lam / c) / 2 * s ≤ lam - c * gt K c lam s := by
  rw [lam_sub_cgt hc hlam hK hs]
  have hcl : 0 < c / lam := div_pos hc hlam
  have hKs := mul_nonneg hK hs
  have hKs' : K * s ≤ c / lam := by
    rw [le_div_iff₀ hlam]; nlinarith
  calc lam * K * (lam / c) / 2 * s = lam * K * s / (2 * (c / lam)) := by field_simp
    _ ≤ lam * K * s / (K * s + c / lam) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

lemma gt_anti {K c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hK : 0 ≤ K) {s s' : ℝ}
    (hs : 0 ≤ s) (hss : s ≤ s') : gt K c lam s' ≤ gt K c lam s := by
  have hcl : 0 < c / lam := div_pos hc hlam
  unfold gt
  exact one_div_le_one_div_of_le (by have := mul_nonneg hK hs; linarith)
    (by have := mul_le_mul_of_nonneg_left hss hK; linarith)

lemma gt_sub_le {K c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hK : 0 ≤ K) {s s' : ℝ}
    (hs : 0 ≤ s) (hs' : 0 ≤ s') : |gt K c lam s - gt K c lam s'| ≤ K * (lam / c) ^ 2 * |s - s'| := by
  have hcl : 0 < c / lam := div_pos hc hlam
  have h := inv_sub_inv_le hcl (u := K * s + c / lam) (v := K * s' + c / lam)
    (by have := mul_nonneg hK hs; linarith) (by have := mul_nonneg hK hs'; linarith)
  unfold gt
  rw [one_div_div] at h
  have e : K * s + c / lam - (K * s' + c / lam) = K * (s - s') := by ring
  rw [e, abs_mul, abs_of_nonneg hK] at h
  calc _ ≤ (lam / c) ^ 2 * (K * |s - s'|) := h
    _ = K * (lam / c) ^ 2 * |s - s'| := by ring

noncomputable def DS (c lam K : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) (W : ℝ → ℝ) (s : ℝ) : ℝ :=
  sInf ((fun b => PhiS c lam K cb ν W s b) '' Icc 0 1)

/-- Bounds for `DS` on the invariant set `B/4 q ≤ W q ≤ 2B q`, `B = λ K (λ/c)`. -/
lemma DS_facts {c lam K : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hc : 0 < c) (hlam : 0 < lam) (hK : 0 < K) (hcb : ReinsPremium c cb)
    (hcdf : Continuous (cdf ν))
    {P bl : ℝ} (hP : 0 ≤ P) (hbl : 0 < bl) (hbl1 : bl ≤ 1) (hblc : ∀ b ∈ Ico 0 bl, c < cb b)
    (hG : ∀ s, 0 ≤ s → cdf ν s ≤ P * s)
    {s1 : ℝ} (hs1 : s1 ≤ 1) (c1 : lam * K * s1 ≤ c) (c2 : lam * P / bl * s1 ≤ 1 / 4)
    (c3 : lam * (lam / c) * s1 ≤ 1)
    (c4 : 2 * P * (lam * K * (lam / c)) * s1 ≤ bl / 2)
    (c5 : 2 * (lam * K * (lam / c)) * s1 ≤ min (lam / 2) ((cb (bl / 2) - c) * gt K c lam 1))
    {W : ℝ → ℝ} (hW : Continuous W)
    (hWb : ∀ q ∈ Icc 0 s1,
      lam * K * (lam / c) / 4 * q ≤ W q ∧ W q ≤ 2 * (lam * K * (lam / c)) * q)
    {s : ℝ} (hs : s ∈ Icc 0 s1) :
    BddBelow ((fun b => PhiS c lam K cb ν W s b) '' Icc 0 1) ∧
    (∀ b ∈ Ico 0 bl, PhiS c lam K cb ν W s 1 ≤ PhiS c lam K cb ν W s b) ∧
    lam * K * (lam / c) / 4 * s ≤ DS c lam K cb ν W s ∧
    DS c lam K cb ν W s ≤ 2 * (lam * K * (lam / c)) * s := by
  obtain ⟨B, hB⟩ : ∃ B, B = lam * K * (lam / c) := ⟨_, rfl⟩
  rw [← hB] at c4 c5 hWb ⊢
  have hBpos : 0 < B := by rw [hB]; positivity
  have hs0 := hs.1
  have hW0 : ∀ q ∈ Icc 0 s, 0 ≤ W q := fun q hq => by
    have := (hWb q ⟨hq.1, hq.2.trans hs.2⟩).1
    have : 0 ≤ B / 4 * q := mul_nonneg (by positivity) hq.1
    linarith
  have hX0 : 0 ≤ Xof W s := intervalIntegral.integral_nonneg hs0 hW0
  have hXB : Xof W s ≤ B * s ^ 2 := by
    have e : ∫ q in (0:ℝ)..s, 2 * B * q = B * s ^ 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]; ring
    rw [← e]
    exact intervalIntegral.integral_mono_on hs0 (hW.intervalIntegrable _ _)
      ((continuous_const_mul (2 * B)).intervalIntegrable _ _)
      (fun q hq => (hWb q ⟨hq.1, hq.2.trans hs.2⟩).2)
  have hss : s ^ 2 ≤ s1 := by nlinarith [hs.2]
  have hgs := gt_bounds hc hlam hK.le hs0
  have hI : ∀ b, 0 ≤ ∫ q in (0:ℝ)..s, tail ν (Xof W s - Xof W q) b * gt K c lam q * W q :=
    fun b => intervalIntegral.integral_nonneg hs0 (fun q hq =>
      mul_nonneg (mul_nonneg (tail_nonneg ν _ _) (gt_bounds hc hlam hK.le hq.1).1.le) (hW0 q hq))
  have hcgt : c * gt K c lam s ≤ lam := by
    have := mul_le_mul_of_nonneg_left hgs.2 hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at this
  -- every bracket is at least `-λ`
  have hlow : ∀ b ∈ Icc (0:ℝ) 1, -lam ≤ PhiS c lam K cb ν W s b := by
    intro b hb
    have k1 := mul_nonneg hlam.le (tail_nonneg ν (Xof W s) b)
    have k2 := mul_nonneg hlam.le (hI b)
    have k3 := mul_nonneg (cb_nonneg hcb hb) hgs.1.le
    unfold PhiS; nlinarith
  have hBdd : BddBelow ((fun b => PhiS c lam K cb ν W s b) '' Icc 0 1) :=
    ⟨-lam, by rintro _ ⟨b, hb, rfl⟩; exact hlow b hb⟩
  -- the bracket at `b = 1`
  have hup : PhiS c lam K cb ν W s 1 ≤ 2 * B * s := by
    have hI1 : (∫ q in (0:ℝ)..s, tail ν (Xof W s - Xof W q) 1 * gt K c lam q * W q)
        ≤ lam / c * Xof W s := by
      have e : lam / c * Xof W s = ∫ q in (0:ℝ)..s, lam / c * W q :=
        (intervalIntegral.integral_const_mul _ _).symm
      rw [e]
      have hfc : ContinuousOn (fun q => tail ν (Xof W s - Xof W q) 1 * gt K c lam q * W q)
          (uIcc 0 s) :=
        (((tail_continuous hcdf one_ne_zero).comp
          (continuous_const.sub (Xof_continuous hW))).continuousOn.mul
          ((gt_continuousOn hc hlam hK.le).mono (fun q hq => by
            rw [uIcc_of_le hs0] at hq; exact mem_Ici.2 hq.1))).mul hW.continuousOn
      refine intervalIntegral.integral_mono_on hs0 hfc.intervalIntegrable
        ((continuous_const.mul hW).intervalIntegrable _ _) (fun q hq => ?_)
      have hg := gt_bounds hc hlam hK.le hq.1
      have h1 : tail ν (Xof W s - Xof W q) 1 * gt K c lam q ≤ lam / c := by
        calc _ ≤ 1 * (lam / c) :=
              mul_le_mul (tail_le_one ν _ _) hg.2 hg.1.le zero_le_one
          _ = lam / c := one_mul _
      exact mul_le_mul_of_nonneg_right h1 (hW0 q hq)
    have k1 := tail_le_one ν (Xof W s) 1
    have k2 := lam_sub_cgt_le hc hlam hK.le hs0
    rw [← hB] at k2
    have k3 : lam * (lam / c * Xof W s) ≤ B * s := by
      have : lam * (lam / c) * Xof W s ≤ lam * (lam / c) * (B * s ^ 2) :=
        mul_le_mul_of_nonneg_left hXB (by positivity)
      have h2 : lam * (lam / c) * s ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hs.2 (by positivity)) c3
      nlinarith
    have k4 := mul_le_mul_of_nonneg_left hI1 hlam.le
    have k5 := mul_le_mul_of_nonneg_left k1 hlam.le
    unfold PhiS
    rw [hcb.2.2.1]
    linarith
  -- brackets with `b < b̲` are large
  have hhigh2 : ∀ b ∈ Ico 0 bl, 2 * B * s ≤ PhiS c lam K cb ν W s b := by
    intro b hb
    have hxs : 2 * P * Xof W s ≤ bl / 2 := by
      have : 2 * P * Xof W s ≤ 2 * P * (B * s1) :=
        mul_le_mul_of_nonneg_left (hXB.trans (mul_le_mul_of_nonneg_left hss hBpos.le)) (by positivity)
      linarith
    have k := bracket_ge_high (ν := ν) hlam hcb hbl hbl1 hblc hG hX0 hxs (hI b) hgs.1.le hb
    have hg1 : gt K c lam 1 ≤ gt K c lam s := gt_anti hc hlam hK.le hs0 (hs.2.trans hs1)
    have hcbl : 0 ≤ cb (bl / 2) - c := by
      have := hblc (bl / 2) ⟨by linarith, by linarith⟩; linarith
    have hm : min (lam / 2) ((cb (bl / 2) - c) * gt K c lam 1)
        ≤ min (lam / 2) ((cb (bl / 2) - c) * gt K c lam s) :=
      min_le_min le_rfl (mul_le_mul_of_nonneg_left hg1 hcbl)
    have : 2 * B * s ≤ 2 * B * s1 := mul_le_mul_of_nonneg_left hs.2 (by positivity)
    show _ ≤ lam * tail ν (Xof W s) b
      + lam * (∫ q in (0:ℝ)..s, tail ν (Xof W s - Xof W q) b * gt K c lam q * W q)
      - (c - cb b) * gt K c lam s
    linarith
  have hhigh : ∀ b ∈ Ico 0 bl, PhiS c lam K cb ν W s 1 ≤ PhiS c lam K cb ν W s b :=
    fun b hb => hup.trans (hhigh2 b hb)
  refine ⟨hBdd, hhigh, ?_, (csInf_le hBdd ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩).trans hup⟩
  -- lower bound `B s / 4`
  refine le_csInf ((nonempty_Icc.2 zero_le_one).image _) ?_
  rintro _ ⟨b, hb, rfl⟩
  have hBs : B / 4 * s ≤ 2 * B * s := by nlinarith
  rcases lt_or_ge b bl with h | h
  · exact hBs.trans (hhigh2 b ⟨hb.1, h⟩)
  · have k := bracket_ge_low (ν := ν) hlam hcb hP hbl hG hX0 (hI b) hgs.1.le ⟨h, hb.2⟩
    have k2 := lam_sub_cgt_ge hc hlam hK.le hs0 (le_trans (mul_le_mul_of_nonneg_left hs.2
      (by positivity)) c1)
    rw [← hB] at k2
    have k3 : lam * P * Xof W s / bl ≤ B / 4 * s := by
      have e : lam * P * Xof W s / bl = (lam * P / bl) * Xof W s := by ring
      rw [e]
      have h1 : (lam * P / bl) * Xof W s ≤ (lam * P / bl) * (B * s ^ 2) :=
        mul_le_mul_of_nonneg_left hXB (by positivity)
      have h2 : lam * P / bl * s ≤ 1 / 4 :=
        le_trans (mul_le_mul_of_nonneg_left hs.2 (by positivity)) c2
      nlinarith
    show _ ≤ lam * tail ν (Xof W s) b
      + lam * (∫ q in (0:ℝ)..s, tail ν (Xof W s - Xof W q) b * gt K c lam q * W q)
      - (c - cb b) * gt K c lam s
    linarith

/-- Lipschitz dependence of the bracket on `s`, uniformly in `b ≥ b̲`. -/
lemma PhiS_lip_s {c lam K : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hc : 0 < c) (hlam : 0 < lam) (hK : 0 ≤ K) (hcb : ReinsPremium c cb)
    (hcdf : Continuous (cdf ν)) {P bl b : ℝ} (hbl : 0 < bl) (hb : b ∈ Icc bl 1) (hP : 0 ≤ P)
    (hT : ∀ x x' : ℝ, |tail ν x b - tail ν x' b| ≤ P / bl * |x - x'|)
    {W : ℝ → ℝ} (hW : Continuous W) {s1 M : ℝ} (hM : ∀ q ∈ Icc 0 s1, |W q| ≤ M)
    {s s' : ℝ} (hs' : 0 ≤ s') (hss : s' ≤ s) (hs1 : s ≤ s1) :
    |PhiS c lam K cb ν W s b - PhiS c lam K cb ν W s' b| ≤
      (lam * (P / bl * M) + lam * (P / bl * M * (lam / c) * M * s1 + lam / c * M)
        + (c + cb 0) * (K * (lam / c) ^ 2)) * (s - s') := by
  have hb0 : b ≠ 0 := (hbl.trans_le hb.1).ne'
  have hs0 : 0 ≤ s := hs'.trans hss
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 ⟨le_rfl, hs0.trans hs1⟩)
  have hPb : 0 ≤ P / bl := div_nonneg hP hbl.le
  have hcl : 0 ≤ lam / c := (div_pos hlam hc).le
  have hds : 0 ≤ s - s' := by linarith
  -- increments of `X`
  have hX : ∀ u v, 0 ≤ v → v ≤ u → u ≤ s1 → |Xof W u - Xof W v| ≤ M * (u - v) := by
    intro u v hv hvu hu
    unfold Xof
    rw [intervalIntegral.integral_interval_sub_left (hW.intervalIntegrable _ _)
      (hW.intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := v) (b := u) (C := M)
      (f := W) (fun x hx => by
        rw [uIoc_of_le hvu] at hx
        rw [Real.norm_eq_abs]; exact hM x ⟨by linarith [hx.1], hx.2.trans hu⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ u - v)] at this
    exact this
  have hXs := hX s s' hs' hss hs1
  -- the integrands
  have hfc : ∀ u, ContinuousOn (fun q => tail ν (Xof W u - Xof W q) b * gt K c lam q * W q)
      (Ici 0) := fun u =>
    (((tail_continuous hcdf hb0).comp (continuous_const.sub (Xof_continuous hW))).continuousOn.mul
      (gt_continuousOn hc hlam hK)).mul hW.continuousOn
  have hii : ∀ u v w, 0 ≤ v → v ≤ w → IntervalIntegrable
      (fun q => tail ν (Xof W u - Xof W q) b * gt K c lam q * W q) volume v w := by
    intro u v w hv hvw
    refine ((hfc u).mono ?_).intervalIntegrable
    intro q hq; rw [uIcc_of_le hvw] at hq; exact mem_Ici.2 (hv.trans hq.1)
  have hsplit : (∫ q in (0:ℝ)..s, tail ν (Xof W s - Xof W q) b * gt K c lam q * W q)
      - ∫ q in (0:ℝ)..s', tail ν (Xof W s' - Xof W q) b * gt K c lam q * W q
      = (∫ q in (0:ℝ)..s', (tail ν (Xof W s - Xof W q) b * gt K c lam q * W q
          - tail ν (Xof W s' - Xof W q) b * gt K c lam q * W q))
        + ∫ q in s'..s, tail ν (Xof W s - Xof W q) b * gt K c lam q * W q := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii s 0 s' le_rfl hs')
      (hii s s' s hs' hss), intervalIntegral.integral_sub (hii s 0 s' le_rfl hs')
      (hii s' 0 s' le_rfl hs')]
    ring
  have hI1 : |∫ q in (0:ℝ)..s', (tail ν (Xof W s - Xof W q) b * gt K c lam q * W q
          - tail ν (Xof W s' - Xof W q) b * gt K c lam q * W q)|
      ≤ (P / bl * M * (lam / c) * M * s1) * (s - s') := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := s')
      (C := P / bl * (M * (s - s')) * (lam / c) * M)
      (f := fun q => tail ν (Xof W s - Xof W q) b * gt K c lam q * W q
          - tail ν (Xof W s' - Xof W q) b * gt K c lam q * W q) (fun q hq => by
        rw [uIoc_of_le hs'] at hq
        have hqI : q ∈ Icc 0 s1 := ⟨hq.1.le, hq.2.trans (hss.trans hs1)⟩
        have hg := gt_bounds hc hlam hK hq.1.le
        have e : tail ν (Xof W s - Xof W q) b * gt K c lam q * W q
            - tail ν (Xof W s' - Xof W q) b * gt K c lam q * W q
            = (tail ν (Xof W s - Xof W q) b - tail ν (Xof W s' - Xof W q) b)
              * gt K c lam q * W q := by ring
        have h1 : |tail ν (Xof W s - Xof W q) b - tail ν (Xof W s' - Xof W q) b|
            ≤ P / bl * (M * (s - s')) := by
          refine (hT _ _).trans (mul_le_mul_of_nonneg_left ?_ hPb)
          rw [show Xof W s - Xof W q - (Xof W s' - Xof W q) = Xof W s - Xof W s' by ring]
          exact hXs
        rw [Real.norm_eq_abs, e, abs_mul, abs_mul, abs_of_pos hg.1]
        exact mul_le_mul (mul_le_mul h1 hg.2 hg.1.le (by positivity)) (hM q hqI)
          (abs_nonneg _) (by positivity))
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs'] at this
    calc _ ≤ P / bl * (M * (s - s')) * (lam / c) * M * s' := this
      _ ≤ P / bl * (M * (s - s')) * (lam / c) * M * s1 :=
          mul_le_mul_of_nonneg_left (hss.trans hs1) (by positivity)
      _ = _ := by ring
  have hI2 : |∫ q in s'..s, tail ν (Xof W s - Xof W q) b * gt K c lam q * W q|
      ≤ (lam / c * M) * (s - s') := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s') (b := s)
      (C := lam / c * M) (f := fun q => tail ν (Xof W s - Xof W q) b * gt K c lam q * W q)
      (fun q hq => by
        rw [uIoc_of_le hss] at hq
        have hqI : q ∈ Icc 0 s1 := ⟨by linarith [hq.1], hq.2.trans hs1⟩
        have hg := gt_bounds hc hlam hK hqI.1
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hg.1,
          abs_of_nonneg (tail_nonneg ν _ _)]
        calc _ ≤ 1 * (lam / c) * M :=
              mul_le_mul (mul_le_mul (tail_le_one ν _ _) hg.2 hg.1.le zero_le_one) (hM q hqI)
                (abs_nonneg _) (by positivity)
          _ = lam / c * M := by ring)
    rw [Real.norm_eq_abs, abs_of_nonneg hds] at this
    exact this
  have htl : |tail ν (Xof W s) b - tail ν (Xof W s') b| ≤ P / bl * M * (s - s') := by
    calc _ ≤ P / bl * |Xof W s - Xof W s'| := hT _ _
      _ ≤ P / bl * (M * (s - s')) := mul_le_mul_of_nonneg_left hXs hPb
      _ = _ := by ring
  have hgs := gt_sub_le hc hlam hK hs0 hs'
  rw [abs_of_nonneg hds] at hgs
  have hcbb := cb_nonneg hcb ⟨(hbl.trans_le hb.1).le, hb.2⟩
  have hcbl : cb b ≤ cb 0 := hcb.1 ⟨le_rfl, zero_le_one⟩ ⟨(hbl.trans_le hb.1).le, hb.2⟩
    (hbl.trans_le hb.1).le
  have hc0 : |c - cb b| ≤ c + cb 0 := by rw [abs_le]; constructor <;> linarith
  unfold PhiS
  have e : lam * tail ν (Xof W s) b
      + lam * (∫ q in (0:ℝ)..s, tail ν (Xof W s - Xof W q) b * gt K c lam q * W q)
      - (c - cb b) * gt K c lam s
      - (lam * tail ν (Xof W s') b
      + lam * (∫ q in (0:ℝ)..s', tail ν (Xof W s' - Xof W q) b * gt K c lam q * W q)
      - (c - cb b) * gt K c lam s')
      = lam * (tail ν (Xof W s) b - tail ν (Xof W s') b)
        + lam * ((∫ q in (0:ℝ)..s, tail ν (Xof W s - Xof W q) b * gt K c lam q * W q)
          - ∫ q in (0:ℝ)..s', tail ν (Xof W s' - Xof W q) b * gt K c lam q * W q)
        - (c - cb b) * (gt K c lam s - gt K c lam s') := by ring
  rw [e, hsplit]
  have a1 : |lam * (tail ν (Xof W s) b - tail ν (Xof W s') b)| ≤ lam * (P / bl * M * (s - s')) := by
    rw [abs_mul, abs_of_pos hlam]; exact mul_le_mul_of_nonneg_left htl hlam.le
  have a2 : |lam * ((∫ q in (0:ℝ)..s', (tail ν (Xof W s - Xof W q) b * gt K c lam q * W q
          - tail ν (Xof W s' - Xof W q) b * gt K c lam q * W q))
        + ∫ q in s'..s, tail ν (Xof W s - Xof W q) b * gt K c lam q * W q)|
      ≤ lam * ((P / bl * M * (lam / c) * M * s1) * (s - s') + (lam / c * M) * (s - s')) := by
    rw [abs_mul, abs_of_pos hlam]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hI1 hI2)) hlam.le
  have a3 : |(c - cb b) * (gt K c lam s - gt K c lam s')|
      ≤ (c + cb 0) * (K * (lam / c) ^ 2 * (s - s')) := by
    rw [abs_mul]; exact mul_le_mul hc0 hgs (abs_nonneg _) (by linarith)
  calc _ ≤ |lam * (tail ν (Xof W s) b - tail ν (Xof W s') b)
        + lam * ((∫ q in (0:ℝ)..s', (tail ν (Xof W s - Xof W q) b * gt K c lam q * W q
          - tail ν (Xof W s' - Xof W q) b * gt K c lam q * W q))
        + ∫ q in s'..s, tail ν (Xof W s - Xof W q) b * gt K c lam q * W q)|
        + |(c - cb b) * (gt K c lam s - gt K c lam s')| := abs_sub _ _
    _ ≤ _ := by
      have := (abs_add_le _ _).trans (add_le_add a1 a2)
      have h := add_le_add this a3
      refine h.trans (le_of_eq ?_)
      ring

set_option maxHeartbeats 1000000 in
/-- E1 core: a fixed point `W = DS(W)` on `[0, s1]` in the invariant set (Banach). -/
lemma E1_fixed {c lam K : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hc : 0 < c) (hlam : 0 < lam) (hK : 0 < K) (hcb : ReinsPremium c cb)
    (hcdf : Continuous (cdf ν))
    {P bl : ℝ} (hP : 0 ≤ P) (hbl : 0 < bl) (hbl1 : bl ≤ 1) (hblc : ∀ b ∈ Ico 0 bl, c < cb b)
    (hG : ∀ s, 0 ≤ s → cdf ν s ≤ P * s)
    (hT : ∀ b, bl ≤ b → ∀ x x' : ℝ, |tail ν x b - tail ν x' b| ≤ P / bl * |x - x'|) :
    ∃ s1 > 0, ∃ W : ℝ → ℝ, Continuous W ∧
      (∀ q ∈ Icc 0 s1,
        lam * K * (lam / c) / 4 * q ≤ W q ∧ W q ≤ 2 * (lam * K * (lam / c)) * q) ∧
      ∀ s ∈ Icc 0 s1, W s = DS c lam K cb ν W s := by
  set B := lam * K * (lam / c) with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  have hcbl : 0 < cb (bl / 2) - c := by
    have := hblc (bl / 2) ⟨by linarith, by linarith⟩; linarith
  have hm0 : 0 < min (lam / 2) ((cb (bl / 2) - c) * gt K c lam 1) :=
    lt_min (by linarith) (mul_pos hcbl (gt_bounds hc hlam hK.le zero_le_one).1)
  have hPb : 0 ≤ P / bl := div_nonneg hP hbl.le
  have E : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s ∧ s ≤ 1 ∧ lam * K * s ≤ c ∧ lam * P / bl * s ≤ 1 / 4 ∧
      lam * (lam / c) * s ≤ 1 ∧ 2 * P * B * s ≤ bl / 2 ∧
      2 * B * s ≤ min (lam / 2) ((cb (bl / 2) - c) * gt K c lam 1) ∧
      lam * (P / bl) * s ≤ 1 / 6 ∧ lam * (P / bl) * 2 * (lam / c) * (2 * B) * s ≤ 1 / 6 ∧
      lam * (lam / c) * s ≤ 1 / 6 := by
    filter_upwards [self_mem_nhdsWithin, ev_small 1 1 one_pos, ev_small (lam * K) c hc,
      ev_small (lam * P / bl) (1 / 4) (by norm_num), ev_small (lam * (lam / c)) 1 one_pos,
      ev_small (2 * P * B) (bl / 2) (by positivity), ev_small (2 * B) _ hm0,
      ev_small (lam * (P / bl)) (1 / 6) (by norm_num),
      ev_small (lam * (P / bl) * 2 * (lam / c) * (2 * B)) (1 / 6) (by norm_num),
      ev_small (lam * (lam / c)) (1 / 6) (by norm_num)] with s h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨mem_Ioi.1 h0, by linarith, h2.le, h3.le, h4.le, h5.le, h6.le, h7.le, h8.le, h9.le⟩
  obtain ⟨s1, hs1, hs11, c1, c2, c3, c4, c5, k1, k2, k3⟩ := E.exists
  have h01 : (0:ℝ) ≤ s1 := hs1.le
  -- the invariant set
  obtain ⟨S, hS⟩ : ∃ S : Set C(Icc (0:ℝ) s1, ℝ),
      S = {V | ∀ q : Icc (0:ℝ) s1, B / 4 * (q:ℝ) ≤ V q ∧ V q ≤ 2 * B * (q:ℝ)} := ⟨_, rfl⟩
  have hmemS : ∀ V, V ∈ S ↔ ∀ q : Icc (0:ℝ) s1, B / 4 * (q:ℝ) ≤ V q ∧ V q ≤ 2 * B * (q:ℝ) := by
    intro V; rw [hS]; rfl
  have hSc : IsClosed S := by
    have e : S = ⋂ q : Icc (0:ℝ) s1, ({V : C(Icc (0:ℝ) s1, ℝ) | B / 4 * (q:ℝ) ≤ V q}
        ∩ {V | V q ≤ 2 * B * (q:ℝ)}) := by
      ext V; rw [hmemS]; simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [e]
    exact isClosed_iInter fun q =>
      (isClosed_le continuous_const (continuous_eval_const q)).inter
        (isClosed_le (continuous_eval_const q) continuous_const)
  have hWeq : ∀ V : C(Icc (0:ℝ) s1, ℝ), ∀ q (hq : q ∈ Icc (0:ℝ) s1),
      IccExtend h01 V q = V ⟨q, hq⟩ := fun V q hq => IccExtend_of_mem h01 V hq
  have hWb : ∀ V ∈ S, ∀ q ∈ Icc (0:ℝ) s1,
      B / 4 * q ≤ IccExtend h01 V q ∧ IccExtend h01 V q ≤ 2 * B * q := by
    intro V hV q hq
    rw [hWeq V q hq]; exact (hmemS V).1 hV ⟨q, hq⟩
  have hWM : ∀ V ∈ S, ∀ q ∈ Icc (0:ℝ) s1, |IccExtend h01 V q| ≤ 2 * B * s1 := by
    intro V hV q hq
    have h := hWb V hV q hq
    have h0 : 0 ≤ B / 4 * q := mul_nonneg (by positivity) hq.1
    have h1 : 2 * B * q ≤ 2 * B * s1 := mul_le_mul_of_nonneg_left hq.2 (by positivity)
    rw [abs_of_nonneg (by linarith)]; linarith
  have facts : ∀ V ∈ S, ∀ s ∈ Icc (0:ℝ) s1,
      BddBelow ((fun b => PhiS c lam K cb ν (IccExtend h01 V) s b) '' Icc 0 1) ∧
      (∀ b ∈ Ico 0 bl, PhiS c lam K cb ν (IccExtend h01 V) s 1
        ≤ PhiS c lam K cb ν (IccExtend h01 V) s b) ∧
      B / 4 * s ≤ DS c lam K cb ν (IccExtend h01 V) s ∧
      DS c lam K cb ν (IccExtend h01 V) s ≤ 2 * B * s := fun V hV s hs =>
    DS_facts hc hlam hK hcb hcdf hP hbl hbl1 hblc hG hs11 c1 c2 c3 (by rw [← hB]; linarith)
      c5 V.continuous.Icc_extend' (hWb V hV) hs
  -- `DS` is Lipschitz in `s`
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = lam * (P / bl * (2 * B * s1))
      + lam * (P / bl * (2 * B * s1) * (lam / c) * (2 * B * s1) * s1 + lam / c * (2 * B * s1))
      + (c + cb 0) * (K * (lam / c) ^ 2) := ⟨_, rfl⟩
  have hDSlip : ∀ V ∈ S, ∀ s ∈ Icc (0:ℝ) s1, ∀ s' ∈ Icc (0:ℝ) s1, s' ≤ s →
      |DS c lam K cb ν (IccExtend h01 V) s - DS c lam K cb ν (IccExtend h01 V) s'|
        ≤ L * (s - s') := by
    intro V hV s hs s' hs' hss
    obtain ⟨hB1, hh1, -, -⟩ := facts V hV s hs
    obtain ⟨hB2, hh2, -, -⟩ := facts V hV s' hs'
    unfold DS
    refine sInf_sub_abs_le hbl.le hbl1 hB1 hB2 hh1 hh2 (fun b hb => ?_)
    rw [hL]
    exact PhiS_lip_s hc hlam hK.le hcb hcdf hbl hb hP (hT b hb.1) V.continuous.Icc_extend'
      (hWM V hV) hs'.1 hss hs.2
  have hDSc : ∀ V ∈ S, ContinuousOn (DS c lam K cb ν (IccExtend h01 V)) (Icc 0 s1) := by
    intro V hV
    refine (LipschitzOnWith.of_dist_le' (K := L) (fun x hx y hy => ?_)).continuousOn
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total y x with h | h
    · rw [abs_of_nonneg (by linarith : 0 ≤ x - y)]; exact hDSlip V hV x hx y hy h
    · rw [abs_sub_comm x y, abs_of_nonneg (by linarith : 0 ≤ y - x), abs_sub_comm]
      exact hDSlip V hV y hy x hx h
  -- the map
  have hTm : ∀ V : S, ∃ V' : S, ∀ q : Icc (0:ℝ) s1,
      V'.1 q = DS c lam K cb ν (IccExtend h01 V.1) q := by
    intro V
    let V' : C(Icc (0:ℝ) s1, ℝ) := ⟨fun q => DS c lam K cb ν (IccExtend h01 V.1) q,
      (hDSc V.1 V.2).comp_continuous continuous_subtype_val (fun q => q.2)⟩
    refine ⟨⟨V', (hmemS V').2 (fun q => ?_)⟩, fun q => rfl⟩
    obtain ⟨-, -, h1, h2⟩ := facts V.1 V.2 q q.2
    exact ⟨h1, h2⟩
  choose T hTdef using hTm
  have hcontr : ∀ V1 V2 : S, dist (T V1) (T V2) ≤ (1 / 2) * dist V1 V2 := by
    intro V1 V2
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have hN : 0 ≤ ‖V1.1 - V2.1‖ := norm_nonneg _
    refine (ContinuousMap.norm_le _ (by positivity)).2 (fun q => ?_)
    rw [ContinuousMap.sub_apply, hTdef V1 q, hTdef V2 q, Real.norm_eq_abs]
    obtain ⟨hB1, hh1, -, -⟩ := facts V1.1 V1.2 q q.2
    obtain ⟨hB2, hh2, -, -⟩ := facts V2.1 V2.2 q q.2
    unfold DS
    refine sInf_sub_abs_le hbl.le hbl1 hB1 hB2 hh1 hh2 (fun b hb => ?_)
    have hq := q.2
    have hδ : ∀ q' ∈ Icc (0:ℝ) q, |IccExtend h01 V1.1 q' - IccExtend h01 V2.1 q'|
        ≤ ‖V1.1 - V2.1‖ := by
      intro q' hq'
      have hq'I : q' ∈ Icc (0:ℝ) s1 := ⟨hq'.1, hq'.2.trans hq.2⟩
      rw [hWeq V1.1 q' hq'I, hWeq V2.1 q' hq'I]
      have := (V1.1 - V2.1).norm_coe_le_norm ⟨q', hq'I⟩
      rwa [ContinuousMap.sub_apply, Real.norm_eq_abs] at this
    have hM : ∀ q' ∈ Icc (0:ℝ) q, |IccExtend h01 V1.1 q'| ≤ 2 * B * s1 :=
      fun q' hq' => hWM V1.1 V1.2 q' ⟨hq'.1, hq'.2.trans hq.2⟩
    refine (PhiS_sub_le hc hlam hK.le hcdf hbl hb.1 hP (hT b hb.1) V1.1.continuous.Icc_extend'
      V2.1.continuous.Icc_extend' hq.1 hM hδ).trans ?_
    set δ := ‖V1.1 - V2.1‖
    set s := (q:ℝ)
    have hs0 : 0 ≤ s := hq.1
    have hs1' : s ≤ s1 := hq.2
    have e : lam * (P / bl * (δ * s))
        + lam * ((P / bl * (2 * (δ * s)) * (lam / c) * (2 * B * s1) + (lam / c) * δ) * s)
        = δ * (lam * (P / bl) * s + lam * (P / bl) * 2 * (lam / c) * (2 * B) * (s1 * s ^ 2)
          + lam * (lam / c) * s) := by ring
    rw [e]
    have a1 : lam * (P / bl) * s ≤ 1 / 6 :=
      le_trans (mul_le_mul_of_nonneg_left hs1' (by positivity)) k1
    have hss : s1 * s ^ 2 ≤ s1 := by
      have : s ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have a2 : lam * (P / bl) * 2 * (lam / c) * (2 * B) * (s1 * s ^ 2) ≤ 1 / 6 :=
      le_trans (mul_le_mul_of_nonneg_left hss (by positivity)) k2
    have a3 : lam * (lam / c) * s ≤ 1 / 6 :=
      le_trans (mul_le_mul_of_nonneg_left hs1' (by positivity)) k3
    have : lam * (P / bl) * s + lam * (P / bl) * 2 * (lam / c) * (2 * B) * (s1 * s ^ 2)
        + lam * (lam / c) * s ≤ 1 / 2 := by linarith
    calc _ ≤ δ * (1 / 2) := mul_le_mul_of_nonneg_left this hN
      _ = 1 / 2 * δ := by ring
  haveI : CompleteSpace S := hSc.completeSpace_coe
  have hV0 : (⟨fun q => B * (q:ℝ), continuous_const.mul continuous_subtype_val⟩ :
      C(Icc (0:ℝ) s1, ℝ)) ∈ S := by
    rw [hmemS]
    intro q
    have := q.2.1
    constructor
    · show B / 4 * (q:ℝ) ≤ B * (q:ℝ); nlinarith
    · show B * (q:ℝ) ≤ 2 * B * (q:ℝ); nlinarith
  haveI : Nonempty S := ⟨⟨_, hV0⟩⟩
  let Kc : NNReal := ⟨1 / 2, by norm_num⟩
  have hTc : ContractingWith Kc T :=
    ⟨by rw [← NNReal.coe_lt_coe]; show (1 / 2 : ℝ) < (1 : NNReal); norm_num,
      LipschitzWith.of_dist_le_mul (fun V1 V2 => hcontr V1 V2)⟩
  set Vst := ContractingWith.fixedPoint T hTc with hVst
  have hfix : T Vst = Vst := ContractingWith.fixedPoint_isFixedPt hTc
  refine ⟨s1, hs1, IccExtend h01 Vst.1, Vst.1.continuous.Icc_extend', hWb Vst.1 Vst.2,
    fun s hs => ?_⟩
  have := hTdef Vst ⟨s, hs⟩
  rw [hfix] at this
  rw [hWeq Vst.1 s hs]
  exact this

/-- Change of variables `x = X q` (1-D Jacobian formula; no integrability needed). -/
lemma integral_cov {X V F : ℝ → ℝ} {σ : ℝ} (hσ : 0 ≤ σ) (hX0 : X 0 = 0)
    (hXd : ∀ q ∈ Icc 0 σ, HasDerivWithinAt X (V q) (Icc 0 σ) q)
    (hmono : StrictMonoOn X (Icc 0 σ)) (hV : ∀ q ∈ Icc 0 σ, 0 ≤ V q) :
    ∫ x in (0:ℝ)..X σ, F x = ∫ q in (0:ℝ)..σ, V q * F (X q) := by
  have hcont : ContinuousOn X (Icc 0 σ) := fun q hq => (hXd q hq).continuousWithinAt
  have h0 : (0:ℝ) ∈ Icc 0 σ := ⟨le_rfl, hσ⟩
  have hs : σ ∈ Icc 0 σ := ⟨hσ, le_rfl⟩
  have hXσ : 0 ≤ X σ := by
    rcases eq_or_lt_of_le hσ with h | h
    · rw [← h, hX0]
    · rw [← hX0]; exact (hmono h0 hs h).le
  have himg : X '' Icc 0 σ = Icc 0 (X σ) := by
    apply Subset.antisymm
    · rintro _ ⟨q, hq, rfl⟩
      rw [← hX0]
      exact ⟨hmono.monotoneOn h0 hq hq.1, hmono.monotoneOn hq hs hq.2⟩
    · have := hcont.surjOn_Icc h0 hs
      rwa [hX0] at this
  have hI := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hXd hmono.injOn F
  rw [himg] at hI
  rw [intervalIntegral.integral_of_le hXσ, intervalIntegral.integral_of_le hσ,
    ← integral_Icc_eq_integral_Ioc, hI, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc (fun q hq => ?_)
  simp only [smul_eq_mul, abs_of_nonneg (hV q hq)]

lemma gt_strictAnti {K c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hK : 0 < K) {s s' : ℝ}
    (hs : 0 ≤ s) (hss : s < s') : gt K c lam s' < gt K c lam s := by
  have hcl : 0 < c / lam := div_pos hc hlam
  unfold gt
  exact one_div_lt_one_div_of_lt (by have := mul_nonneg hK.le hs; linarith)
    (by have := mul_lt_mul_of_pos_left hss hK; linarith)

/-- E1: local existence at `0`: a strictly decreasing solution of (5) on some `[0, a]`, `a > 0`,
with `den g a > 0` (the hypotheses of `extend_step`). -/
lemma E1_local {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : ReinsPremium c cb) (hν : ClaimLaw ν)
    (hdens : SchmidliRuin.Exist.HasBoundedDensity ν) :
    ∃ a > 0, ∃ g : ℝ → ℝ, StrictAntiOn g (Icc 0 a) ∧
      SolvesEq5On c lam mu sigma cb ν g (Icc 0 a) ∧ ContinuousOn g (Icc 0 a) ∧
      (∀ z ∈ Icc 0 a, 0 ≤ g z ∧ g z ≤ lam / c) ∧ 0 < g a ∧ 0 < den c lam cb ν g a := by
  haveI : IsProbabilityMeasure ν := hν.1
  have hcdf : Continuous (cdf ν) := hν.2.2
  obtain ⟨p, -, ⟨P, hp⟩, hνp⟩ := hdens
  have hP : 0 ≤ P := le_trans (hp 0).1 (hp 0).2
  obtain ⟨bl, hbl, hbl1, hblc, -⟩ := hcb.2.2.2.2
  obtain ⟨K, hKd⟩ : ∃ K : ℝ, K = mu ^ 2 / (2 * sigma ^ 2) := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hKd]; positivity
  have hG : ∀ s, 0 ≤ s → cdf ν s ≤ P * s := fun s hs => cdf_le_mul hν.2.1 hp hνp hs
  have hT : ∀ b, bl ≤ b → ∀ x x' : ℝ, |tail ν x b - tail ν x' b| ≤ P / bl * |x - x'| :=
    fun b hb x x' => tail_lip hp hνp hbl hb x x'
  obtain ⟨s1, hs1, W, hWc, hWb, hWfix⟩ := E1_fixed hc hlam hK hcb hcdf hP hbl hbl1 hblc hG hT
  have hB : 0 < lam * K * (lam / c) := by positivity
  have hWpos : ∀ q ∈ Ioc 0 s1, 0 < W q := fun q hq =>
    lt_of_lt_of_le (mul_pos (by positivity) hq.1) (hWb q ⟨hq.1.le, hq.2⟩).1
  have hW0 : ∀ q ∈ Icc 0 s1, 0 ≤ W q := fun q hq =>
    le_trans (mul_nonneg (by positivity) hq.1) (hWb q hq).1
  have hXd : ∀ q, HasDerivAt (Xof W) (W q) q := fun q =>
    (hWc.integral_hasStrictDerivAt 0 q).hasDerivAt
  have hX0 : Xof W 0 = 0 := intervalIntegral.integral_same
  have hXmono : StrictMonoOn (Xof W) (Icc 0 s1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 s1)
      (fun q _ => (hXd q).continuousAt.continuousWithinAt) (fun q hq => ?_)
    rw [interior_Icc] at hq
    rw [(hXd q).deriv]; exact hWpos q ⟨hq.1, hq.2.le⟩
  have hXcont : ContinuousOn (Xof W) (Icc 0 s1) := fun q _ =>
    (hXd q).continuousAt.continuousWithinAt
  have h0 : (0:ℝ) ∈ Icc 0 s1 := ⟨le_rfl, hs1.le⟩
  have hs1m : s1 ∈ Icc 0 s1 := ⟨hs1.le, le_rfl⟩
  have hapos : 0 < Xof W s1 := by rw [← hX0]; exact hXmono h0 hs1m hs1
  have himg : Xof W '' Icc 0 s1 = Icc 0 (Xof W s1) := by
    apply Subset.antisymm
    · rintro _ ⟨q, hq, rfl⟩
      rw [← hX0]
      exact ⟨hXmono.monotoneOn h0 hq hq.1, hXmono.monotoneOn hq hs1m hq.2⟩
    · have := hXcont.surjOn_Icc h0 hs1m
      rwa [hX0] at this
  obtain ⟨inv, hinv⟩ : ∃ inv : ℝ → ℝ, inv = Function.invFunOn (Xof W) (Icc 0 s1) := ⟨_, rfl⟩
  have hinv_mem : ∀ x ∈ Icc 0 (Xof W s1), inv x ∈ Icc 0 s1 := fun x hx => by
    rw [← himg] at hx; rw [hinv]; exact Function.invFunOn_mem hx
  have hinv_eq : ∀ x ∈ Icc 0 (Xof W s1), Xof W (inv x) = x := fun x hx => by
    rw [← himg] at hx; rw [hinv]; exact Function.invFunOn_eq hx
  have hinv_X : ∀ q ∈ Icc 0 s1, inv (Xof W q) = q := fun q hq => by
    rw [hinv]; exact hXmono.injOn.leftInvOn_invFunOn hq
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun x => gt K c lam (inv x) := ⟨_, rfl⟩
  have hgX : ∀ q ∈ Icc 0 s1, g (Xof W q) = gt K c lam q := fun q hq => by
    rw [hg]; simp only [hinv_X q hq]
  -- `den g` along `X` is `W`
  have hden : ∀ s ∈ Icc 0 s1, den c lam cb ν g (Xof W s) = W s := by
    intro s hs
    rw [hWfix s hs]
    unfold den DS
    congr 1
    refine Set.image_congr (fun b _ => ?_)
    have hcov := integral_cov (F := fun z => tail ν (Xof W s - z) b * g z) hs.1 hX0
      (fun q _ => (hXd q).hasDerivWithinAt) (hXmono.mono (Icc_subset_Icc le_rfl hs.2))
      (fun q hq => hW0 q ⟨hq.1, hq.2.trans hs.2⟩)
    beta_reduce at hcov
    have e : ∫ q in (0:ℝ)..s, W q * (tail ν (Xof W s - Xof W q) b * g (Xof W q))
        = ∫ q in (0:ℝ)..s, tail ν (Xof W s - Xof W q) b * gt K c lam q * W q := by
      refine intervalIntegral.integral_congr (fun q hq => ?_)
      rw [uIcc_of_le hs.1] at hq
      simp only [hgX q ⟨hq.1, hq.2.trans hs.2⟩]; ring
    unfold PhiS
    rw [hcov, e, hgX s hs]
    ring
  -- `∫_0^{X σ} den⁻¹ = σ`
  have hcovI : ∀ σ ∈ Icc 0 s1,
      IntervalIntegrable (fun x => (den c lam cb ν g x)⁻¹) volume 0 (Xof W σ) ∧
      ∫ x in (0:ℝ)..Xof W σ, (den c lam cb ν g x)⁻¹ = σ := by
    intro σ hσ
    refine integral_inv_cov (V := W) hσ.1 hX0 (fun q _ => (hXd q).hasDerivWithinAt)
      (hXmono.mono (Icc_subset_Icc le_rfl hσ.2)) (fun q hq => ?_)
    have hqI : q ∈ Icc 0 s1 := ⟨hq.1.le, hq.2.trans hσ.2⟩
    have hWq := hWpos q ⟨hq.1, hq.2.trans hσ.2⟩
    show |W q| * (den c lam cb ν g (Xof W q))⁻¹ = 1
    rw [hden q hqI, abs_of_pos hWq, mul_inv_cancel₀ hWq.ne']
  have hinvint : ∀ x ∈ Icc 0 (Xof W s1), ∫ t in (0:ℝ)..x, (den c lam cb ν g t)⁻¹ = inv x := by
    intro x hx
    have := (hcovI (inv x) (hinv_mem x hx)).2
    rwa [hinv_eq x hx] at this
  have hinvc : ContinuousOn inv (Icc 0 (Xof W s1)) := by
    have h1 := (hcovI s1 hs1m).1
    have h2 := intervalIntegral.continuousOn_primitive_interval' h1 left_mem_uIcc
    rw [uIcc_of_le hapos.le] at h2
    exact h2.congr (fun x hx => (hinvint x hx).symm)
  have hgc : ContinuousOn g (Icc 0 (Xof W s1)) := by
    rw [hg]
    exact (gt_continuousOn hc hlam hK.le).comp hinvc (fun x hx => mem_Ici.2 (hinv_mem x hx).1)
  have hanti : StrictAntiOn g (Icc 0 (Xof W s1)) := by
    intro x hx y hy hxy
    have hlt : inv x < inv y := by
      by_contra hle
      push Not at hle
      have := hXmono.monotoneOn (hinv_mem y hy) (hinv_mem x hx) hle
      rw [hinv_eq x hx, hinv_eq y hy] at this
      linarith
    rw [hg]
    exact gt_strictAnti hc hlam hK (hinv_mem x hx).1 hlt
  refine ⟨Xof W s1, hapos, g, hanti, fun u hu => ?_, hgc, fun z hz => ?_, ?_, ?_⟩
  · have hσ := hinv_mem u hu
    have hXσ := hinv_eq u hu
    refine ⟨(hgc.mono (Icc_subset_Icc le_rfl hu.2)).intervalIntegrable_of_Icc hu.1,
      fun x hx => ?_, ?_, ?_⟩
    · have hxI : x ∈ Icc 0 (Xof W s1) := ⟨hx.1.le, hx.2.le.trans hu.2⟩
      have hq := hinv_mem x hxI
      have hqx := hinv_eq x hxI
      have hq0 : 0 < inv x := by
        refine lt_of_le_of_ne hq.1 (fun h => ?_)
        rw [← h, hX0] at hqx
        linarith [hx.1]
      rw [← hqx, hden _ hq]
      exact (hWpos _ ⟨hq0, hq.2⟩).ne'
    · have := (hcovI _ hσ).1; rwa [hXσ] at this
    · have := (hcovI _ hσ).2
      rw [hXσ] at this
      rw [this, ← hKd, hg]
      rfl
  · rw [hg]
    have := gt_bounds hc hlam hK.le (hinv_mem z hz).1 (K := K)
    exact ⟨this.1.le, this.2⟩
  · rw [hg]; exact (gt_bounds hc hlam hK.le (hinv_mem _ ⟨hapos.le, le_rfl⟩).1).1
  · rw [hden s1 hs1m]; exact hWpos s1 ⟨hs1, le_rfl⟩

/-! ## E4 bricks (session 4) -/

/-- (5) on `I` depends on `g` only through its values on `[0, u]`, `u ∈ I`. -/
lemma solves_congr {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g h : ℝ → ℝ} {I : Set ℝ}
    (hI : ∀ u ∈ I, 0 ≤ u) (hEq : ∀ u ∈ I, EqOn g h (Icc 0 u))
    (hs : SolvesEq5On c lam mu sigma cb ν g I) : SolvesEq5On c lam mu sigma cb ν h I := by
  intro u hu
  obtain ⟨h1, h2, h3, h4⟩ := hs u hu
  have hu0 := hI u hu
  have hE := hEq u hu
  have hden : ∀ x ∈ Icc 0 u, den c lam cb ν g x = den c lam cb ν h x := fun x hx =>
    den_congr hx.1 (fun z hz => hE ⟨hz.1, hz.2.trans hx.2⟩)
  have hden' : EqOn (fun x => (den c lam cb ν g x)⁻¹) (fun x => (den c lam cb ν h x)⁻¹)
      (Icc 0 u) := fun x hx => by simp only [hden x hx]
  refine ⟨?_, fun x hx => ?_, ?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hu0] at h1 ⊢
    exact h1.congr_fun hE measurableSet_Icc
  · rw [← hden x ⟨hx.1.le, hx.2.le⟩]; exact h2 x hx
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hu0] at h3 ⊢
    exact h3.congr_fun hden' measurableSet_Icc
  · have hi : ∫ x in (0:ℝ)..u, (den c lam cb ν g x)⁻¹ = ∫ x in (0:ℝ)..u, (den c lam cb ν h x)⁻¹ := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [uIcc_of_le hu0] at hx
      exact hden' hx
    rw [← hE ⟨hu0, le_rfl⟩, h4, hi]


/-! ### E4 (session 5): general basics on a down-closed set of capitals -/

lemma gy {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ} {I : Set ℝ}
    (hs : SolvesEq5On c lam mu sigma cb ν g I) {u : ℝ} (hu : u ∈ I) :
    g u = 1 / yfun c lam mu sigma cb ν g u :=
  (hs u hu).2.2.2

lemma gyfun_continuousOn {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    {I : Set ℝ} (hs : SolvesEq5On c lam mu sigma cb ν g I) {U : ℝ} (hU : U ∈ I) (hU0 : 0 ≤ U) :
    ContinuousOn (yfun c lam mu sigma cb ν g) (Icc 0 U) := by
  have h1 := (hs U hU).2.2.1
  have h2 : ContinuousOn (fun u => ∫ x in (0 : ℝ)..u, (den c lam cb ν g x)⁻¹) (uIcc 0 U) :=
    intervalIntegral.continuousOn_primitive_interval' h1 left_mem_uIcc
  rw [uIcc_of_le hU0] at h2
  exact (continuousOn_const.mul h2).add continuousOn_const

lemma gsol_bounds {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ} {I : Set ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hI : ∀ u ∈ I, Icc 0 u ⊆ I) (hI0 : ∀ u ∈ I, 0 ≤ u)
    (hg : StrictAntiOn g I) (hs : SolvesEq5On c lam mu sigma cb ν g I)
    {u : ℝ} (hu : u ∈ I) :
    c / lam ≤ yfun c lam mu sigma cb ν g u ∧ 0 < g u ∧ g u ≤ lam / c := by
  have hu0 : 0 ≤ u := hI0 u hu
  have hy0 := yfun_zero c lam mu sigma cb ν g
  have hcl : 0 < c / lam := div_pos hc hlam
  have h0I : (0:ℝ) ∈ I := hI u hu ⟨le_rfl, hu0⟩
  have hg0 : g 0 = lam / c := by
    rw [gy hs h0I, hy0, one_div_div]
  have key : c / lam ≤ yfun c lam mu sigma cb ν g u := by
    by_contra hlt
    push Not at hlt
    rcases eq_or_lt_of_le hu0 with h0 | hpos
    · subst h0; rw [hy0] at hlt; exact lt_irrefl _ hlt
    have hgu0 : g u < g 0 := hg h0I hu hpos
    by_cases hyp : 0 < yfun c lam mu sigma cb ν g u
    · have : lam / c < g u := by
        rw [gy hs hu, ← one_div_div c lam]
        exact one_div_lt_one_div_of_lt hyp hlt
      linarith
    · push Not at hyp
      have hcont := gyfun_continuousOn hs hu hu0
      have hmem : c / (2 * lam) ∈
          Icc (yfun c lam mu sigma cb ν g u) (yfun c lam mu sigma cb ν g 0) := by
        rw [hy0]
        have h2 : 0 < c / (2 * lam) := div_pos hc (by linarith)
        have h3 : c / (2 * lam) < c / lam := div_lt_div_of_pos_left hc hlam (by linarith)
        exact ⟨by linarith, h3.le⟩
      obtain ⟨t, ht, hyt⟩ := intermediate_value_Icc' hu0 hcont hmem
      have htI : t ∈ I := hI u hu ht
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [hy0] at hyt
        have : c / (2 * lam) < c / lam := div_lt_div_of_pos_left hc hlam (by linarith)
        linarith
      have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hgt0 : g t < g 0 := hg h0I htI htpos
      have : g t = 2 * lam / c := by
        rw [gy hs htI, hyt, one_div_div]
      rw [this, hg0] at hgt0
      have : lam / c < 2 * lam / c := div_lt_div_of_pos_right (by linarith) hc
      linarith
  have hypos : 0 < yfun c lam mu sigma cb ν g u := lt_of_lt_of_le hcl key
  refine ⟨key, ?_, ?_⟩
  · rw [gy hs hu]; exact one_div_pos.2 hypos
  · rw [gy hs hu, ← one_div_div c lam]
    exact one_div_le_one_div_of_le hcl key

lemma gsol_continuousOn {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    {I : Set ℝ} (hc : 0 < c) (hlam : 0 < lam) (hI : ∀ u ∈ I, Icc 0 u ⊆ I)
    (hI0 : ∀ u ∈ I, 0 ≤ u)
    (hg : StrictAntiOn g I) (hs : SolvesEq5On c lam mu sigma cb ν g I)
    {U : ℝ} (hU : U ∈ I) : ContinuousOn g (Icc 0 U) := by
  have hcont := gyfun_continuousOn hs hU (hI0 U hU)
  have hne : ∀ x ∈ Icc (0 : ℝ) U, yfun c lam mu sigma cb ν g x ≠ 0 := fun x hx =>
    ne_of_gt (lt_of_lt_of_le (div_pos hc hlam) (gsol_bounds hc hlam hI hI0 hg hs (hI U hU hx)).1)
  exact (continuousOn_const.div hcont hne).congr (fun x hx => gy hs (hI U hU hx))

lemma gyfun_strictMonoOn {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    {I : Set ℝ} (hc : 0 < c) (hlam : 0 < lam) (hI : ∀ u ∈ I, Icc 0 u ⊆ I)
    (hI0 : ∀ u ∈ I, 0 ≤ u)
    (hg : StrictAntiOn g I) (hs : SolvesEq5On c lam mu sigma cb ν g I) :
    StrictMonoOn (yfun c lam mu sigma cb ν g) I := by
  intro a ha b hb hab
  have hya := gsol_bounds hc hlam hI hI0 hg hs ha
  have hyb := gsol_bounds hc hlam hI hI0 hg hs hb
  have hgab : g b < g a := hg ha hb hab
  have hpa : 0 < yfun c lam mu sigma cb ν g a := lt_of_lt_of_le (div_pos hc hlam) hya.1
  have hpb : 0 < yfun c lam mu sigma cb ν g b := lt_of_lt_of_le (div_pos hc hlam) hyb.1
  rw [gy hs ha, gy hs hb] at hgab
  exact (one_div_lt_one_div hpb hpa).1 hgab

lemma gyfun_sub {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ} {I : Set ℝ}
    (hs : SolvesEq5On c lam mu sigma cb ν g I) {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) :
    yfun c lam mu sigma cb ν g b - yfun c lam mu sigma cb ν g a =
      mu ^ 2 / (2 * sigma ^ 2) * ∫ x in a..b, (den c lam cb ν g x)⁻¹ := by
  have h := intervalIntegral.integral_interval_sub_left (hs b hb).2.2.1 (hs a ha).2.2.1
  unfold yfun
  rw [← h]
  ring

lemma gden_continuousAt {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    {I : Set ℝ} (hc : 0 < c) (hlam : 0 < lam) (hcb : ReinsPremium c cb) (hν : ClaimLaw ν)
    (hI : ∀ u ∈ I, Icc 0 u ⊆ I) (hI0 : ∀ u ∈ I, 0 ≤ u)
    (hg : StrictAntiOn g I) (hs : SolvesEq5On c lam mu sigma cb ν g I)
    {u x : ℝ} (hu : u ∈ I) (hx : 0 < x) (hxu : x < u) :
    ContinuousAt (den c lam cb ν g) x := by
  haveI := hν.1
  have hu0 : 0 ≤ u := hI0 u hu
  have hgc := gsol_continuousOn hc hlam hI hI0 hg hs hu
  set gh : ℝ → ℝ := fun z => g (min z u) with hgh
  have hmap : ∀ z : ℝ, 0 ≤ z → min z u ∈ Icc 0 u := fun z hz =>
    ⟨le_min hz hu0, min_le_right _ _⟩
  have hghc : ContinuousOn gh (Ici 0) :=
    hgc.comp (continuous_id.min continuous_const).continuousOn (fun z hz => hmap z hz)
  have hb := fun z (hz : (0:ℝ) ≤ z) => gsol_bounds hc hlam hI hI0 hg hs (hI u hu (hmap z hz))
  have hcont := den_continuousOn_of hc hlam hcb hν.2.2 hghc (fun z hz => (hb z hz).2.1.le)
    (fun z hz => (hb z hz).2.2)
  have hca : ContinuousAt (den c lam cb ν gh) x := hcont.continuousAt (Ioi_mem_nhds hx)
  refine hca.congr ?_
  filter_upwards [Ioo_mem_nhds hx hxu] with y hy
  refine den_congr hy.1.le (fun z hz => ?_)
  show g (min z u) = g z
  rw [min_eq_left (hz.2.trans hy.2.le)]

lemma gden_pos {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    {I : Set ℝ} (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : ReinsPremium c cb) (hν : ClaimLaw ν)
    (hI : ∀ u ∈ I, Icc 0 u ⊆ I) (hI0 : ∀ u ∈ I, 0 ≤ u)
    (hg : StrictAntiOn g I) (hs : SolvesEq5On c lam mu sigma cb ν g I)
    {u x : ℝ} (hu : u ∈ I) (hx : 0 < x) (hxu : x < u) :
    0 < den c lam cb ν g x := by
  have hne : den c lam cb ν g x ≠ 0 := (hs u hu).2.1 x ⟨hx, hxu⟩
  by_contra hle
  push Not at hle
  have hneg : den c lam cb ν g x < 0 := lt_of_le_of_ne hle hne
  have hca := gden_continuousAt hc hlam hcb hν hI hI0 hg hs hu hx hxu
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hca.eventually (gt_mem_nhds hneg))
  have hm : 0 < min ε (u - x) := lt_min hε (by linarith)
  set b := x + min ε (u - x) / 2 with hbdef
  have hxb : x < b := by linarith
  have hbu : b < u := by linarith [min_le_right ε (u - x)]
  have hbI : b ∈ I := hI u hu ⟨by linarith, hbu.le⟩
  have hxI : x ∈ I := hI u hu ⟨hx.le, hxu.le⟩
  have hint : IntervalIntegrable (fun t => (den c lam cb ν g t)⁻¹) volume x b := by
    refine ((hs b hbI).2.2.1).mono_set ?_
    rw [uIcc_of_le hxb.le, uIcc_of_le (by linarith : (0 : ℝ) ≤ b)]
    exact Icc_subset_Icc hx.le le_rfl
  have hpos : 0 < ∫ t in x..b, -(den c lam cb ν g t)⁻¹ := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hint.neg ?_ hxb
    intro t ht
    have hd : dist t x < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [ht.1, ht.2, min_le_left ε (u - x)]
    have := hball hd
    simp only [Left.neg_pos_iff, inv_lt_zero]
    exact this
  rw [intervalIntegral.integral_neg] at hpos
  have hK : 0 < mu ^ 2 / (2 * sigma ^ 2) := by positivity
  have hsub := gyfun_sub hs hxI hbI
  have hmono := gyfun_strictMonoOn hc hlam hI hI0 hg hs hxI hbI hxb
  have : mu ^ 2 / (2 * sigma ^ 2) * ∫ t in x..b, (den c lam cb ν g t)⁻¹ < 0 :=
    mul_neg_of_pos_of_neg hK (by linarith)
  linarith

/-! ### E4: lower bounds on the brackets away from `0` -/

lemma tail_mono_b (ν : Measure ℝ) {x b b' : ℝ} (hx : 0 ≤ x) (hb' : 0 < b') (hbb : b' ≤ b) :
    tail ν x b' ≤ tail ν x b := by
  have hb : 0 < b := lt_of_lt_of_le hb' hbb
  simp only [tail, if_neg hb'.ne', if_neg hb.ne']
  have : x / b ≤ x / b' := div_le_div_of_nonneg_left hx hb' hbb
  linarith [monotone_cdf ν this]

lemma tail_near_zero {ν : Measure ℝ} [IsProbabilityMeasure ν] (hneg : ν (Iic 0) = 0)
    (hcdf : Continuous (cdf ν)) {b : ℝ} (hb : 0 < b) :
    ∃ δ > 0, ∀ t ∈ Icc (0:ℝ) δ, 1 / 2 ≤ tail ν t b := by
  have h0 : tail ν 0 b = 1 := by
    have hc0 : cdf ν 0 = 0 := by rw [cdf_eq_real, measureReal_def, hneg]; simp
    simp only [tail, if_neg hb.ne', zero_div, hc0, sub_zero]
  have hcont : ContinuousAt (fun t => tail ν t b) 0 := (tail_continuous hcdf hb.ne').continuousAt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
    (hcont.eventually (lt_mem_nhds (show (1:ℝ)/2 < tail ν 0 b by rw [h0]; norm_num)))
  refine ⟨ε / 2, by linarith, fun t ht => (hball ?_).le⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
  linarith [ht.2]

lemma conv_ge_sub {ν : Measure ℝ} [IsProbabilityMeasure ν] {g : ℝ → ℝ} {t b a1 a2 m : ℝ}
    (hb : 0 ≤ b) (ha1 : 0 ≤ a1) (ha12 : a1 ≤ a2) (ha2 : a2 ≤ t)
    (hgc : ContinuousOn g (Icc 0 t)) (hg0 : ∀ z ∈ Icc (0:ℝ) t, 0 ≤ g z)
    (hlow : ∀ z ∈ Icc a1 a2, 1 / 2 ≤ tail ν (t - z) b ∧ m ≤ g z) (hm : 0 ≤ m) :
    (a2 - a1) * m / 2 ≤ conv ν g t b := by
  have ht : 0 ≤ t := ha1.trans (ha12.trans ha2)
  have hF : ∀ u v : ℝ, u ∈ Icc 0 t → v ∈ Icc 0 t →
      IntervalIntegrable (fun z => tail ν (t - z) b * g z) volume u v := by
    intro u v hu hv
    refine (tail_sub_intervalIntegrable ν hb t u v).mul_continuousOn (hgc.mono ?_)
    intro z hz
    rcases le_total u v with h | h
    · rw [uIcc_of_le h] at hz; exact ⟨hu.1.trans hz.1, hz.2.trans hv.2⟩
    · rw [uIcc_of_ge h] at hz; exact ⟨hv.1.trans hz.1, hz.2.trans hu.2⟩
  have m0 : (0:ℝ) ∈ Icc 0 t := ⟨le_rfl, ht⟩
  have m1 : a1 ∈ Icc 0 t := ⟨ha1, ha12.trans ha2⟩
  have m2 : a2 ∈ Icc 0 t := ⟨ha1.trans ha12, ha2⟩
  have mt : t ∈ Icc 0 t := ⟨ht, le_rfl⟩
  have hsplit : conv ν g t b = (∫ z in (0:ℝ)..a1, tail ν (t - z) b * g z)
      + (∫ z in a1..a2, tail ν (t - z) b * g z) + ∫ z in a2..t, tail ν (t - z) b * g z := by
    unfold conv
    rw [intervalIntegral.integral_add_adjacent_intervals (hF 0 a1 m0 m1) (hF a1 a2 m1 m2),
      intervalIntegral.integral_add_adjacent_intervals (hF 0 a2 m0 m2) (hF a2 t m2 mt)]
  have hn1 : 0 ≤ ∫ z in (0:ℝ)..a1, tail ν (t - z) b * g z :=
    intervalIntegral.integral_nonneg ha1 (fun z hz => mul_nonneg (tail_nonneg ν _ _)
      (hg0 z ⟨hz.1, hz.2.trans (ha12.trans ha2)⟩))
  have hn3 : 0 ≤ ∫ z in a2..t, tail ν (t - z) b * g z :=
    intervalIntegral.integral_nonneg ha2 (fun z hz => mul_nonneg (tail_nonneg ν _ _)
      (hg0 z ⟨(ha1.trans ha12).trans hz.1, hz.2⟩))
  have hmid : ∫ z in a1..a2, m / 2 ≤ ∫ z in a1..a2, tail ν (t - z) b * g z := by
    refine intervalIntegral.integral_mono_on ha12 intervalIntegrable_const (hF a1 a2 m1 m2) ?_
    intro z hz
    have h := hlow z hz
    have := mul_le_mul h.1 h.2 hm (tail_nonneg ν _ _)
    linarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmid
  rw [hsplit]
  nlinarith

lemma phi_low_b {c lam : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν] {g : ℝ → ℝ}
    (hlam : 0 < lam) (hcb : ReinsPremium c cb) {bl : ℝ} (hbl : 0 < bl) (hbl1 : bl ≤ 1)
    (hblc : ∀ b ∈ Ico 0 bl, c < cb b) {d t : ℝ} (hd : 0 < d) (hdt : d ≤ t)
    (hδ : ∀ s ∈ Icc (0:ℝ) d, 1 / 2 ≤ tail ν s (bl / 2))
    (hgc : ContinuousOn g (Icc 0 t)) (hg0 : ∀ z ∈ Icc (0:ℝ) t, 0 ≤ g z)
    (hgt : ∀ z ∈ Icc (0:ℝ) t, g t ≤ g z) {b : ℝ} (hb : b ∈ Ico 0 bl) :
    min (cb (bl / 2) - c) (lam * d / 2) * g t ≤ phi c lam cb ν g t b := by
  rw [phi_expand]
  have ht0 : 0 ≤ t := le_trans hd.le hdt
  have hgt0 : 0 ≤ g t := hg0 t ⟨ht0, le_rfl⟩
  have htail := mul_nonneg hlam.le (tail_nonneg ν t b)
  have hconv := mul_nonneg hlam.le (conv_nonneg (ν := ν) (b := b) ht0 hg0)
  rcases lt_or_ge b (bl / 2) with hb2 | hb2
  · have h1 : cb (bl / 2) ≤ cb b :=
      hcb.1 ⟨hb.1, by linarith [hb.2]⟩ ⟨by linarith, by linarith⟩ hb2.le
    have h2 := mul_le_mul_of_nonneg_right (min_le_left (cb (bl / 2) - c) (lam * d / 2)) hgt0
    have h3 := mul_le_mul_of_nonneg_right h1 hgt0
    nlinarith
  · have hbpos : 0 < b := by linarith
    have hcbb : c < cb b := hblc b hb
    have hcv : (t - (t - d)) * g t / 2 ≤ conv ν g t b := by
      refine conv_ge_sub hbpos.le (by linarith) (by linarith) le_rfl hgc hg0 ?_ hgt0
      intro z hz
      refine ⟨le_trans (hδ (t - z) ⟨by linarith [hz.2], by linarith [hz.1]⟩)
        (tail_mono_b ν (by linarith [hz.2]) (by linarith) hb2), hgt z ⟨by linarith [hz.1], hz.2⟩⟩
    have h2 := mul_le_mul_of_nonneg_right (min_le_right (cb (bl / 2) - c) (lam * d / 2)) hgt0
    have h4 := mul_le_mul_of_nonneg_left hcv hlam.le
    have h5 := mul_nonneg (sub_pos.2 hcbb).le hgt0
    nlinarith


/-! ### E4: a half-open solution on `[0,S)` stays away from `0` and closes at `S` -/

lemma Ico_down {S : ℝ} : ∀ u ∈ Ico (0:ℝ) S, Icc 0 u ⊆ Ico 0 S :=
  fun _ hu _ hz => ⟨hz.1, lt_of_le_of_lt hz.2 hu.2⟩

lemma Ico_nonneg {S : ℝ} : ∀ u ∈ Ico (0:ℝ) S, 0 ≤ u := fun _ hu => hu.1

set_option maxHeartbeats 1000000 in
lemma HS_lower {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : ReinsPremium c cb) (hν : ClaimLaw ν) {S : ℝ} (hS : 0 < S)
    (hg : StrictAntiOn g (Ico 0 S)) (hs : SolvesEq5On c lam mu sigma cb ν g (Ico 0 S)) :
    ∃ m > 0, ∀ u ∈ Ico 0 S, m ≤ g u := by
  haveI := hν.1
  have hI := Ico_down (S := S)
  have hI0 := Ico_nonneg (S := S)
  have hB := fun u (hu : u ∈ Ico (0:ℝ) S) => gsol_bounds hc hlam hI hI0 hg hs hu
  have hC := fun u (hu : u ∈ Ico (0:ℝ) S) => gsol_continuousOn hc hlam hI hI0 hg hs hu
  obtain ⟨bl, hbl, hbl1, hblc, hblc2⟩ := hcb.2.2.2.2
  obtain ⟨δ, hδ, hδt⟩ := tail_near_zero hν.2.1 hν.2.2 (show 0 < bl / 2 by linarith)
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = min δ (S / 2) := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; exact lt_min hδ (by linarith)
  have hdδ : d ≤ δ := by rw [hd]; exact min_le_left _ _
  have hdS : d ≤ S / 2 := by rw [hd]; exact min_le_right _ _
  have hδd : ∀ s ∈ Icc (0:ℝ) d, 1 / 2 ≤ tail ν s (bl / 2) := fun s hs =>
    hδt s ⟨hs.1, hs.2.trans hdδ⟩
  obtain ⟨A0, hA0⟩ : ∃ A0 : ℝ, A0 = S - d / 2 := ⟨_, rfl⟩
  have hA0I : A0 ∈ Ico (0:ℝ) S := ⟨by linarith, by linarith⟩
  have hgA0 : 0 < g A0 := (hB A0 hA0I).2.1
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = d / 2 * g A0 / 2 := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hθ1 : 0 < cb (bl / 2) - c := sub_pos.2 (hblc (bl / 2) ⟨by linarith, by linarith⟩)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = min (cb (bl / 2) - c) (lam * d / 2) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; exact lt_min hθ1 (by positivity)
  have hden : ∀ A ∈ Ico A0 S, min (θ * g A) (lam * κ - c * g A) ≤ den c lam cb ν g A := by
    intro A hA
    have hAI : A ∈ Ico (0:ℝ) S := ⟨by linarith [hA.1], hA.2⟩
    have hgc := hC A hAI
    have hg0 : ∀ z ∈ Icc (0:ℝ) A, 0 ≤ g z := fun z hz => (hB z (hI A hAI hz)).2.1.le
    have hgt : ∀ z ∈ Icc (0:ℝ) A, g A ≤ g z := fun z hz =>
      hg.antitoneOn (hI A hAI hz) hAI hz.2
    refine den_ge_min (bl := bl) (fun b hb => ?_) (fun b hb => ?_)
    · have := phi_low_b hlam hcb hbl hbl1 hblc hd0 (by linarith [hA.1]) hδd hgc hg0 hgt hb
      rw [← hθ] at this
      exact this
    · rw [phi_expand]
      have hbpos : 0 < b := lt_of_lt_of_le hbl hb.1
      have hcv : (A - d / 2 - (A - d)) * g A0 / 2 ≤ conv ν g A b := by
        refine conv_ge_sub hbpos.le (by linarith [hA.1]) (by linarith) (by linarith) hgc hg0 ?_
          hgA0.le
        intro z hz
        refine ⟨le_trans (hδd (A - z) ⟨by linarith [hz.2], by linarith [hz.1]⟩)
          (tail_mono_b ν (by linarith [hz.2]) (by linarith) (by linarith [hb.1])), ?_⟩
        exact hg.antitoneOn (hI A hAI ⟨by linarith [hz.1, hA.1], by linarith [hz.2]⟩) hA0I
          (by linarith [hz.2, hA.2])
      have e : (A - d / 2 - (A - d)) * g A0 / 2 = κ := by rw [hκ]; ring
      rw [e] at hcv
      have hgA := (hB A hAI).2.1.le
      have h1 := mul_nonneg hlam.le (tail_nonneg ν A b)
      have h2 := mul_nonneg (cb_nonneg hcb ⟨hbl.le.trans hb.1, hb.2⟩) hgA
      have h3 := mul_le_mul_of_nonneg_left hcv hlam.le
      have h4 := min_le_right (θ * g A) (lam * κ - c * g A)
      linarith
  obtain ⟨K, hKd⟩ : ∃ K : ℝ, K = mu ^ 2 / (2 * sigma ^ 2) := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hKd]; positivity
  obtain ⟨gs, hgs⟩ : ∃ gs : ℝ, gs = lam * κ / (c + θ) := ⟨_, rfl⟩
  have hgs0 : 0 < gs := by rw [hgs]; positivity
  have hgsm : (c + θ) * gs = lam * κ := by rw [hgs]; field_simp
  by_cases hcase : ∃ A1 ∈ Ico A0 S, g A1 ≤ gs
  swap
  · push Not at hcase
    refine ⟨gs, hgs0, fun u hu => ?_⟩
    rcases le_or_gt A0 u with h | h
    · exact (hcase u ⟨h, hu.2⟩).le
    · exact (hcase A0 ⟨le_rfl, hA0I.2⟩).le.trans (hg.antitoneOn hu hA0I h.le)
  obtain ⟨A1, hA1, hgA1⟩ := hcase
  have hA1I : A1 ∈ Ico (0:ℝ) S := ⟨by linarith [hA1.1, hA0I.1], hA1.2⟩
  have hgA1p : 0 < g A1 := (hB A1 hA1I).2.1
  have hden2 : ∀ x ∈ Ico A1 S, θ * g x ≤ den c lam cb ν g x := by
    intro x hx
    have hxI : x ∈ Ico (0:ℝ) S := ⟨by linarith [hx.1, hA1I.1], hx.2⟩
    have h1 := hden x ⟨le_trans hA1.1 hx.1, hx.2⟩
    have hgx : g x ≤ gs := (hg.antitoneOn hA1I hxI hx.1).trans hgA1
    have hgx0 := (hB x hxI).2.1
    have h2 : θ * g x ≤ lam * κ - c * g x := by
      have := mul_le_mul_of_nonneg_left hgx (by linarith : (0:ℝ) ≤ c + θ)
      nlinarith
    exact le_trans (le_min le_rfl h2) h1
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = θ / (2 * K) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hstep : ∀ v u, v ∈ Ico A1 S → u ∈ Ico A1 S → v ≤ u → u - v ≤ r → g v / 2 ≤ g u := by
    intro v u hv hu hvu hur
    have hvI : v ∈ Ico (0:ℝ) S := ⟨by linarith [hv.1, hA1I.1], hv.2⟩
    have huI : u ∈ Ico (0:ℝ) S := ⟨by linarith [hu.1, hA1I.1], hu.2⟩
    have hsub := gyfun_sub hs hvI huI
    rw [← hKd] at hsub
    have hyu := gy hs huI
    have hyv := gy hs hvI
    have hYu : 0 < yfun c lam mu sigma cb ν g u := lt_of_lt_of_le (div_pos hc hlam) (hB u huI).1
    have hYv : 0 < yfun c lam mu sigma cb ν g v := lt_of_lt_of_le (div_pos hc hlam) (hB v hvI).1
    set Yu := yfun c lam mu sigma cb ν g u with hYud
    set Yv := yfun c lam mu sigma cb ν g v with hYvd
    have hint : IntervalIntegrable (fun x => (den c lam cb ν g x)⁻¹) volume v u := by
      refine ((hs u huI).2.2.1).mono_set ?_
      rw [uIcc_of_le hvu, uIcc_of_le huI.1]
      exact Icc_subset_Icc hvI.1 le_rfl
    have hbound : ∫ x in v..u, (den c lam cb ν g x)⁻¹ ≤ ∫ x in v..u, Yu / θ := by
      refine intervalIntegral.integral_mono_on hvu hint intervalIntegrable_const ?_
      intro x hx
      have hxI : x ∈ Ico (0:ℝ) S := ⟨by linarith [hx.1, hvI.1], lt_of_le_of_lt hx.2 huI.2⟩
      have h1 := hden2 x ⟨le_trans hv.1 hx.1, hxI.2⟩
      have h2 : g u ≤ g x := hg.antitoneOn hxI huI hx.2
      have h3 : θ / Yu ≤ den c lam cb ν g x := by
        have e : θ / Yu = θ * g u := by rw [hyu]; ring
        rw [e]; nlinarith [mul_le_mul_of_nonneg_left h2 hθ0.le]
      have := inv_anti₀ (div_pos hθ0 hYu) h3
      rwa [inv_div] at this
    rw [intervalIntegral.integral_const, smul_eq_mul] at hbound
    have hK2 : K * ((u - v) * (Yu / θ)) ≤ Yu / 2 := by
      have h5 : K * (u - v) ≤ θ / 2 := by
        have := mul_le_mul_of_nonneg_left hur hK.le
        have e : K * r = θ / 2 := by rw [hr]; field_simp
        linarith
      have e2 : K * ((u - v) * (Yu / θ)) = (K * (u - v)) * Yu / θ := by ring
      rw [e2, div_le_iff₀ hθ0]
      nlinarith
    have hYle : Yu ≤ 2 * Yv := by
      have := mul_le_mul_of_nonneg_left hbound hK.le
      linarith
    rw [hyu, hyv, div_div, one_div_le_one_div (by positivity) hYu]
    linarith
  have hiter : ∀ n : ℕ, ∀ u ∈ Ico A1 S, u ≤ A1 + n * r → g A1 / 2 ^ n ≤ g u := by
    intro n
    induction n with
    | zero =>
      intro u hu hle
      have : u = A1 := le_antisymm (by simpa using hle) hu.1
      rw [this]; simp
    | succ n ih =>
      intro u hu hle
      have hpow : g A1 / 2 ^ (n + 1) ≤ g A1 / 2 ^ n := by
        apply div_le_div_of_nonneg_left hgA1p.le (by positivity)
        exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
      rcases le_or_gt u (A1 + n * r) with h | h
      · exact hpow.trans (ih u hu h)
      · obtain ⟨v, hv⟩ : ∃ v : ℝ, v = A1 + n * r := ⟨_, rfl⟩
        have hnr : (0:ℝ) ≤ n * r := by positivity
        have hv0 : A1 ≤ v := by linarith
        have hvS : v < S := by linarith [hu.2]
        have hvI : v ∈ Ico A1 S := ⟨hv0, hvS⟩
        have h1 := ih v hvI hv.le
        have ec : ((n + 1 : ℕ) : ℝ) * r = n * r + r := by push_cast; ring
        have h2 := hstep v u hvI hu (by linarith) (by linarith)
        have e : g A1 / 2 ^ (n + 1) = g A1 / 2 ^ n / 2 := by rw [pow_succ]; ring
        rw [e]; linarith
  obtain ⟨N, hN⟩ := exists_nat_ge ((S - A1) / r)
  refine ⟨g A1 / 2 ^ N, by positivity, fun u hu => ?_⟩
  rcases le_or_gt A1 u with h | h
  · refine hiter N u ⟨h, hu.2⟩ ?_
    have : S - A1 ≤ N * r := by rwa [div_le_iff₀ hr0] at hN
    linarith [hu.2]
  · have h1 : g A1 / 2 ^ N ≤ g A1 := div_le_self hgA1p.le (one_le_pow₀ (by norm_num))
    exact h1.trans (hg.antitoneOn hu hA1I h.le)

set_option maxHeartbeats 2000000 in
lemma HS_close {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : ReinsPremium c cb) (hν : ClaimLaw ν)
    (hdens : SchmidliRuin.Exist.HasBoundedDensity ν) {S : ℝ} (hS : 0 < S)
    (hg : StrictAntiOn g (Ico 0 S)) (hs : SolvesEq5On c lam mu sigma cb ν g (Ico 0 S)) :
    ∃ g' : ℝ → ℝ, StrictAntiOn g' (Icc 0 S) ∧ SolvesEq5On c lam mu sigma cb ν g' (Icc 0 S) ∧
      ContinuousOn g' (Icc 0 S) ∧ (∀ z ∈ Icc 0 S, 0 ≤ g' z ∧ g' z ≤ lam / c) ∧ 0 < g' S ∧
      0 < den c lam cb ν g' S ∧ EqOn g' g (Ico 0 S) := by
  haveI := hν.1
  have hI := Ico_down (S := S)
  have hI0 := Ico_nonneg (S := S)
  have hB := fun u (hu : u ∈ Ico (0:ℝ) S) => gsol_bounds hc hlam hI hI0 hg hs hu
  have hC := fun u (hu : u ∈ Ico (0:ℝ) S) => gsol_continuousOn hc hlam hI hI0 hg hs hu
  obtain ⟨m, hm0, hm⟩ := HS_lower hc hlam hmu hsigma hcb hν hS hg hs
  have h0I : (0:ℝ) ∈ Ico 0 S := ⟨le_rfl, hS⟩
  have hne : (g '' Ico 0 S).Nonempty := ⟨g 0, mem_image_of_mem g h0I⟩
  have hbdd : BddBelow (g '' Ico 0 S) := ⟨m, by rintro _ ⟨u, hu, rfl⟩; exact hm u hu⟩
  obtain ⟨gS, hgS⟩ : ∃ gS : ℝ, gS = sInf (g '' Ico 0 S) := ⟨_, rfl⟩
  have hgSm : m ≤ gS := by
    rw [hgS]; exact le_csInf hne (by rintro _ ⟨u, hu, rfl⟩; exact hm u hu)
  have hgSle : ∀ u ∈ Ico (0:ℝ) S, gS ≤ g u := fun u hu => by
    rw [hgS]; exact csInf_le hbdd (mem_image_of_mem g hu)
  have hgSlt : ∀ u ∈ Ico (0:ℝ) S, gS < g u := by
    intro u hu
    have hw : (u + S) / 2 ∈ Ico (0:ℝ) S := ⟨by linarith [hu.1, hu.2], by linarith [hu.2]⟩
    exact lt_of_le_of_lt (hgSle _ hw) (hg hu hw (by linarith [hu.2]))
  have hgS0 : 0 < gS := lt_of_lt_of_le hm0 hgSm
  obtain ⟨g', hg'⟩ : ∃ g' : ℝ → ℝ, g' = fun x => if x < S then g x else gS := ⟨_, rfl⟩
  have hg'S : g' S = gS := by rw [hg']; simp
  have hg'eq : EqOn g' g (Ico 0 S) := fun x hx => by rw [hg']; simp [hx.2]
  -- bounds, monotonicity, continuity of g'
  have hb' : ∀ z ∈ Icc (0:ℝ) S, 0 ≤ g' z ∧ g' z ≤ lam / c := by
    intro z hz
    rcases lt_or_eq_of_le hz.2 with h | h
    · rw [hg'eq ⟨hz.1, h⟩]; exact ⟨(hB z ⟨hz.1, h⟩).2.1.le, (hB z ⟨hz.1, h⟩).2.2⟩
    · rw [h, hg'S]; exact ⟨hgS0.le, (hgSle 0 h0I).trans (hB 0 h0I).2.2⟩
  have hanti : StrictAntiOn g' (Icc 0 S) := by
    intro a ha b hb hab
    have haI : a ∈ Ico (0:ℝ) S := ⟨ha.1, lt_of_lt_of_le hab hb.2⟩
    rw [hg'eq haI]
    rcases lt_or_eq_of_le hb.2 with h | h
    · rw [hg'eq ⟨hb.1, h⟩]; exact hg haI ⟨hb.1, h⟩ hab
    · rw [h, hg'S]; exact hgSlt a haI
  have hcont : ContinuousOn g' (Icc 0 S) := by
    intro x hx
    rcases lt_or_eq_of_le hx.2 with h | h
    · obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (x + S) / 2 := ⟨_, rfl⟩
      have huI : u ∈ Ico (0:ℝ) S := ⟨by linarith [hx.1], by linarith⟩
      have h1 : ContinuousWithinAt g' (Icc 0 u) x :=
        ((hC u huI) x ⟨hx.1, by linarith⟩).congr (fun z hz => hg'eq (hI u huI hz))
          (hg'eq ⟨hx.1, h⟩)
      refine h1.mono_of_mem_nhdsWithin ?_
      exact mem_nhdsWithin.2 ⟨Iio u, isOpen_Iio, by show x < u; linarith,
        fun z hz => ⟨hz.2.1, hz.1.le⟩⟩
    · rw [h, Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨_, ⟨u0, hu0, rfl⟩, hlt⟩ :=
        exists_lt_of_csInf_lt hne (show sInf (g '' Ico 0 S) < gS + ε by rw [← hgS]; linarith)
      refine ⟨S - u0, by linarith [hu0.2], ?_⟩
      intro z hz hzd
      rw [Real.dist_eq] at hzd ⊢
      rw [hg'S]
      rcases lt_or_eq_of_le hz.2 with h2 | h2
      · have hzI : z ∈ Ico (0:ℝ) S := ⟨hz.1, h2⟩
        rw [hg'eq hzI]
        have hz0 : u0 < z := by rw [abs_lt] at hzd; linarith [hzd.1]
        have h3 := hg.antitoneOn hu0 hzI hz0.le
        have h4 := hgSle z hzI
        rw [abs_lt]; constructor <;> linarith
      · rw [h2, hg'S, sub_self, abs_zero]; exact hε
  have hden_eq : ∀ x ∈ Ico (0:ℝ) S, den c lam cb ν g' x = den c lam cb ν g x := fun x hx =>
    den_congr hx.1 (fun z hz => hg'eq ⟨hz.1, lt_of_le_of_lt hz.2 hx.2⟩)
  have hsI : SolvesEq5On c lam mu sigma cb ν g' (Ico 0 S) :=
    solves_congr hI0 (fun u hu z hz => (hg'eq (hI u hu hz)).symm) hs
  have hdpos : ∀ x ∈ Ioo (0:ℝ) S, 0 < den c lam cb ν g x := by
    intro x hx
    have hw : (x + S) / 2 ∈ Ico (0:ℝ) S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact gden_pos hc hlam hmu hsigma hcb hν hI hI0 hg hs hw hx.1 (by linarith [hx.2])
  obtain ⟨K, hKd⟩ : ∃ K : ℝ, K = mu ^ 2 / (2 * sigma ^ 2) := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hKd]; positivity
  have hg'0 : ∀ z ∈ Icc (0:ℝ) S, 0 ≤ g' z := fun z hz => (hb' z hz).1
  have hg'S_le : ∀ z ∈ Icc (0:ℝ) S, g' S ≤ g' z := fun z hz =>
    hanti.antitoneOn hz ⟨hS.le, le_rfl⟩ hz.2
  -- den g' S > 0
  have hdenS : 0 < den c lam cb ν g' S := by
    obtain ⟨p, -, ⟨P, hp⟩, hνp⟩ := hdens
    have hP : 0 ≤ P := le_trans (hp 0).1 (hp 0).2
    obtain ⟨bl, hbl, hbl1, hblc, hblc2⟩ := hcb.2.2.2.2
    obtain ⟨δ, hδ, hδt⟩ := tail_near_zero hν.2.1 hν.2.2 (show 0 < bl / 2 by linarith)
    obtain ⟨d, hd⟩ : ∃ d : ℝ, d = min δ S := ⟨_, rfl⟩
    have hd0 : 0 < d := by rw [hd]; exact lt_min hδ hS
    have hdS : d ≤ S := by rw [hd]; exact min_le_right _ _
    have hδd : ∀ s ∈ Icc (0:ℝ) d, 1 / 2 ≤ tail ν s (bl / 2) := fun s hs =>
      hδt s ⟨hs.1, hs.2.trans (by rw [hd]; exact min_le_left _ _)⟩
    have hθ1 : 0 < cb (bl / 2) - c := sub_pos.2 (hblc (bl / 2) ⟨by linarith, by linarith⟩)
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = min (cb (bl / 2) - c) (lam * d / 2) := ⟨_, rfl⟩
    have hθ0 : 0 < θ := by rw [hθ]; exact lt_min hθ1 (by positivity)
    have hlowS : ∀ b ∈ Ico (0:ℝ) bl, θ * gS ≤ phi c lam cb ν g' S b := by
      intro b hb
      have := phi_low_b hlam hcb hbl hbl1 hblc hd0 hdS hδd hcont hg'0 hg'S_le hb
      rwa [hg'S, ← hθ] at this
    obtain ⟨L, hL⟩ : ∃ L : ℝ, L = lam * (P / bl) + lam * (lam / c) := ⟨_, rfl⟩
    have hL0 : 0 < L := by
      have h1 : 0 ≤ lam * (P / bl) := mul_nonneg hlam.le (div_nonneg hP hbl.le)
      have h2 : 0 < lam * (lam / c) := by positivity
      linarith
    have hlip : ∀ b ∈ Icc bl 1, ∀ x ∈ Icc (0:ℝ) S,
        phi c lam cb ν g' x b ≤ phi c lam cb ν g' S b + L * (S - x) := by
      intro b hb x hx
      rw [phi_expand, phi_expand]
      have h1 := tail_lip hp hνp hbl hb.1 x S
      have h2 := conv_sub_le (ν := ν) (g := g') (M := lam / c) (b := b)
        (lt_of_lt_of_le hbl hb.1).le hx.1 hx.2 hcont hg'0 (fun z hz => (hb' z hz).2)
      have h3 : cb b ≤ c := hblc2 b hb
      have h4 : g' S ≤ g' x := hg'S_le x hx
      have h5 : |x - S| = S - x := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith [hx.2])
      rw [h5] at h1
      have h6 := mul_le_mul_of_nonneg_left (abs_le.1 h1).2 hlam.le
      have h7 : conv ν g' x b - conv ν g' S b ≤ lam / c * (S - x) := by
        linarith [(abs_le.1 h2).1]
      have h8 := mul_le_mul_of_nonneg_left h7 hlam.le
      have h9 : (c - cb b) * (g' S - g' x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have e : L * (S - x) = lam * (P / bl * (S - x)) + lam * (lam / c * (S - x)) := by
        rw [hL]; ring
      nlinarith
    by_contra hneg
    push Not at hneg
    obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = 2 / (m * K) := ⟨_, rfl⟩
    have hZ0 : 0 < Z := by rw [hZ]; positivity
    have hmKZ : m * (K * Z) = 2 := by rw [hZ]; field_simp
    obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (L * Z) := ⟨_, rfl⟩
    have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (by positivity)
    obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (θ * m / 2) (L * (S / 2) / (2 * E)) := ⟨_, rfl⟩
    have hε0 : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by positivity)
    have hε1 : ε ≤ θ * m / 2 := by rw [hε]; exact min_le_left _ _
    have hε2 : ε * (2 * E) ≤ L * (S / 2) := by
      have := min_le_right (θ * m / 2) (L * (S / 2) / (2 * E))
      rw [← hε, le_div_iff₀ (by positivity)] at this
      exact this
    -- a near-optimal retention at S
    rw [den_eq_sInf_phi] at hneg
    obtain ⟨_, ⟨b, hb, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt
      ((nonempty_Icc.2 zero_le_one).image _) (lt_of_le_of_lt hneg hε0)
    have hbl' : bl ≤ b := by
      by_contra hb2
      push Not at hb2
      have := hlowS b ⟨hb.1, hb2⟩
      have : θ * m ≤ θ * gS := mul_le_mul_of_nonneg_left hgSm hθ0.le
      nlinarith
    have hdenx : ∀ x ∈ Icc (S / 2) S, x < S →
        den c lam cb ν g x ≤ ε + L * S - L * x := by
      intro x hx hxS
      have hxI : x ∈ Ico (0:ℝ) S := ⟨by linarith [hx.1], hxS⟩
      rw [← hden_eq x hxI]
      have h1 := den_le_phi (ν := ν) (g := g') hc hlam hcb hxI.1 (fun z hz => hg'0 z ⟨hz.1, hz.2.trans hx.2⟩)
        (hb' x ⟨hxI.1, hx.2⟩).2 hb
      have h2 := hlip b ⟨hbl', hb.2⟩ x ⟨hxI.1, hx.2⟩
      linarith
    obtain ⟨u1, hu1⟩ : ∃ u1 : ℝ, u1 = S - ε / L := ⟨_, rfl⟩
    have hεL : ε / L ≤ S / 4 := by
      rw [div_le_iff₀ hL0]
      nlinarith
    have hεL0 : 0 < ε / L := div_pos hε0 hL0
    have hu1a : S / 2 ≤ u1 := by rw [hu1]; linarith
    have hu1S : u1 < S := by rw [hu1]; linarith
    have hu1I : u1 ∈ Ico (0:ℝ) S := ⟨by linarith, hu1S⟩
    have hS2I : S / 2 ∈ Ico (0:ℝ) S := ⟨by linarith, by linarith⟩
    have e1 : ε + L * S - L * u1 = 2 * ε := by rw [hu1]; field_simp; ring
    have e2 : ε + L * S - L * (S / 2) = ε + L * (S / 2) := by ring
    have hpos : ∀ x ∈ Icc (S / 2) u1, 0 < ε + L * S - L * x := by
      intro x hx
      have := mul_le_mul_of_nonneg_left hx.2 hL0.le
      linarith
    have hint1 : IntervalIntegrable (fun x => (ε + L * S - L * x)⁻¹) volume (S / 2) u1 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hu1a]
      exact (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).inv₀
        (fun x hx => (hpos x hx).ne')
    have hint2 : IntervalIntegrable (fun x => (den c lam cb ν g x)⁻¹) volume (S / 2) u1 := by
      refine ((hs u1 hu1I).2.2.1).mono_set ?_
      rw [uIcc_of_le hu1a, uIcc_of_le hu1I.1]
      exact Icc_subset_Icc (by linarith) le_rfl
    have hmono : ∫ x in (S / 2)..u1, (ε + L * S - L * x)⁻¹ ≤
        ∫ x in (S / 2)..u1, (den c lam cb ν g x)⁻¹ := by
      refine intervalIntegral.integral_mono_on hu1a hint1 hint2 ?_
      intro x hx
      have hxS : x < S := lt_of_le_of_lt hx.2 hu1S
      exact inv_anti₀ (hdpos x ⟨by linarith [hx.1], hxS⟩)
        (hdenx x ⟨hx.1, hxS.le⟩ hxS)
    have hcomp := intervalIntegral.integral_comp_sub_mul (a := S / 2) (b := u1)
      (f := fun t : ℝ => t⁻¹) hL0.ne' (ε + L * S)
    rw [e1, e2, integral_inv_of_pos (by positivity) (by positivity), smul_eq_mul] at hcomp
    have hlog : L * Z ≤ Real.log ((ε + L * (S / 2)) / (2 * ε)) := by
      have hr : E ≤ (ε + L * (S / 2)) / (2 * ε) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      have := Real.log_le_log (by positivity) hr
      rwa [hE, Real.log_exp] at this
    have hZle : Z ≤ ∫ x in (S / 2)..u1, (den c lam cb ν g x)⁻¹ := by
      have h1 : Z ≤ L⁻¹ * Real.log ((ε + L * (S / 2)) / (2 * ε)) := by
        rw [← div_eq_inv_mul, le_div_iff₀ hL0]
        linarith
      linarith
    have hsub := gyfun_sub hs hS2I hu1I
    rw [← hKd] at hsub
    have hyS2 := (hB (S / 2) hS2I).1
    have hgu1 := hm u1 hu1I
    rw [gy hs hu1I] at hgu1
    have hY : 0 < yfun c lam mu sigma cb ν g u1 := lt_of_lt_of_le (div_pos hc hlam) (hB u1 hu1I).1
    rw [le_div_iff₀ hY] at hgu1
    have h3 := mul_le_mul_of_nonneg_left hZle hK.le
    have h4 : 0 < c / lam := div_pos hc hlam
    nlinarith
  -- SolvesEq5On on Icc 0 S
  have hS2I : S / 2 ∈ Ico (0:ℝ) S := ⟨by linarith, by linarith⟩
  have hcd : ContinuousOn (den c lam cb ν g') (Icc (S / 2) S) := by
    have hmap : ∀ z : ℝ, 0 ≤ z → min z S ∈ Icc 0 S := fun z hz =>
      ⟨le_min hz hS.le, min_le_right _ _⟩
    have hghc : ContinuousOn (fun z => g' (min z S)) (Ici 0) :=
      hcont.comp (continuous_id.min continuous_const).continuousOn (fun z hz => hmap z hz)
    have hc2 := den_continuousOn_of hc hlam hcb hν.2.2 hghc
      (fun z hz => (hb' _ (hmap z hz)).1) (fun z hz => (hb' _ (hmap z hz)).2)
    refine (hc2.mono (fun x hx => show (0:ℝ) < x by linarith [hx.1])).congr ?_
    intro x hx
    refine den_congr (by linarith [hx.1]) (fun z hz => ?_)
    show g' z = g' (min z S)
    rw [min_eq_left (hz.2.trans hx.2)]
  have hdpos' : ∀ x ∈ Icc (S / 2) S, den c lam cb ν g' x ≠ 0 := by
    intro x hx
    rcases lt_or_eq_of_le hx.2 with h | h
    · rw [hden_eq x ⟨by linarith [hx.1], h⟩]
      exact (hdpos x ⟨by linarith [hx.1], h⟩).ne'
    · rw [h]; exact hdenS.ne'
  have hintS : IntervalIntegrable (fun x => (den c lam cb ν g' x)⁻¹) volume 0 S := by
    have h1 := (hsI (S / 2) hS2I).2.2.1
    have h2 : IntervalIntegrable (fun x => (den c lam cb ν g' x)⁻¹) volume (S / 2) S := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le (by linarith)]
      exact hcd.inv₀ hdpos'
    exact h1.trans h2
  have hFc : ContinuousOn (fun u => g' u * yfun c lam mu sigma cb ν g' u) (Icc 0 S) := by
    have h2 : ContinuousOn (fun u => ∫ x in (0 : ℝ)..u, (den c lam cb ν g' x)⁻¹) (uIcc 0 S) :=
      intervalIntegral.continuousOn_primitive_interval' hintS left_mem_uIcc
    rw [uIcc_of_le hS.le] at h2
    exact hcont.mul ((continuousOn_const.mul h2).add continuousOn_const)
  have hF1 : g' S * yfun c lam mu sigma cb ν g' S = 1 := by
    have hT : Tendsto (fun u => g' u * yfun c lam mu sigma cb ν g' u) (𝓝[<] S)
        (𝓝 (g' S * yfun c lam mu sigma cb ν g' S)) :=
      ((hFc S ⟨hS.le, le_rfl⟩).mono_of_mem_nhdsWithin
        (mem_of_superset (Ioo_mem_nhdsLT hS) Ioo_subset_Icc_self)).tendsto
    have hev : (fun u => g' u * yfun c lam mu sigma cb ν g' u) =ᶠ[𝓝[<] S] fun _ => 1 := by
      filter_upwards [Ioo_mem_nhdsLT hS] with u hu
      have huI : u ∈ Ico (0:ℝ) S := ⟨hu.1.le, hu.2⟩
      have hb2 := gsol_bounds hc hlam hI hI0 (hanti.mono Ico_subset_Icc_self) hsI huI
      have hYp : 0 < yfun c lam mu sigma cb ν g' u := lt_of_lt_of_le (div_pos hc hlam) hb2.1
      rw [gy hsI huI]
      field_simp
    exact tendsto_nhds_unique hT (tendsto_const_nhds.congr' hev.symm)
  have hYS : yfun c lam mu sigma cb ν g' S ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hF1; exact zero_ne_one hF1
  have hsolve : SolvesEq5On c lam mu sigma cb ν g' (Icc 0 S) := by
    intro u hu
    rcases lt_or_eq_of_le hu.2 with h | h
    · exact hsI u ⟨hu.1, h⟩
    · rw [h]
      refine ⟨ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hS.le]; exact hcont),
        fun x hx => ?_, hintS, ?_⟩
      · rw [hden_eq x ⟨hx.1.le, hx.2⟩]; exact (hdpos x hx).ne'
      · show g' S = 1 / yfun c lam mu sigma cb ν g' S
        rw [eq_div_iff hYS]; exact hF1
  exact ⟨g', hanti, hsolve, hcont, hb', by rw [hg'S]; exact hgS0, hdenS, hg'eq⟩


/-! ### E4: global existence by Zorn's lemma -/

/-- Half-open solutions `(S, g)`: `g` is strictly decreasing and solves (5) on `[0, S)`. -/
abbrev HSol (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ) : Type :=
  {p : ℝ × (ℝ → ℝ) // 0 < p.1 ∧ StrictAntiOn p.2 (Ico 0 p.1) ∧
    SolvesEq5On c lam mu sigma cb ν p.2 (Ico 0 p.1)}

/-- Extension order on half-open solutions. -/
abbrev HRel {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ}
    (p q : HSol c lam mu sigma cb ν) : Prop :=
  p.1.1 ≤ q.1.1 ∧ EqOn p.1.2 q.1.2 (Ico 0 p.1.1)

set_option maxHeartbeats 1000000 in
lemma existence {c lam mu sigma : ℝ} {cb : ℝ → ℝ} {ν : Measure ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : ReinsPremium c cb) (hν : ClaimLaw ν)
    (hdens : SchmidliRuin.Exist.HasBoundedDensity ν) :
    ∃ g : ℝ → ℝ, StrictAntiOn g (Ici 0) ∧ SolvesEq5On c lam mu sigma cb ν g (Ici 0) := by
  classical
  by_contra hno
  have htrans : ∀ {a b d : HSol c lam mu sigma cb ν}, HRel a b → HRel b d → HRel a d := by
    intro a b d hab hbd
    exact ⟨hab.1.trans hbd.1,
      fun x hx => (hab.2 hx).trans (hbd.2 ⟨hx.1, lt_of_lt_of_le hx.2 hab.1⟩)⟩
  have hchain : ∀ C : Set (HSol c lam mu sigma cb ν), IsChain HRel C →
      ∃ ub, ∀ a ∈ C, HRel a ub := by
    intro C hC
    rcases C.eq_empty_or_nonempty with hCe | hCne
    · obtain ⟨a, ha, g0, hg0, hs0, -⟩ := E1_local hc hlam hmu hsigma hcb hν hdens
      refine ⟨⟨(a, g0), ha, hg0.mono Ico_subset_Icc_self,
        fun u hu => hs0 u (Ico_subset_Icc_self hu)⟩, ?_⟩
      intro p hp
      rw [hCe] at hp
      exact absurd hp (notMem_empty _)
    obtain ⟨G, hGd⟩ : ∃ G : ℝ → ℝ, G = fun x =>
        if h : ∃ p ∈ C, x < p.1.1 then (Classical.choose h).1.2 x else 0 := ⟨_, rfl⟩
    have hG : ∀ p ∈ C, ∀ x ∈ Ico (0:ℝ) p.1.1, G x = p.1.2 x := by
      intro p hp x hx
      have h : ∃ q ∈ C, x < q.1.1 := ⟨p, hp, hx.2⟩
      have hq := (Classical.choose_spec h).1
      have hxq := (Classical.choose_spec h).2
      have e : G x = (Classical.choose h).1.2 x := by rw [hGd]; simp only [dif_pos h]
      rw [e]
      by_cases hpq : p = Classical.choose h
      · rw [← hpq]
      · rcases hC hp hq hpq with h1 | h1
        · exact (h1.2 hx).symm
        · exact h1.2 ⟨hx.1, hxq⟩
    have hGanti : ∀ x y : ℝ, 0 ≤ x → x < y → (∃ p ∈ C, y < p.1.1) → G y < G x := by
      intro x y hx hxy ⟨p, hp, hyp⟩
      have hxI : x ∈ Ico (0:ℝ) p.1.1 := ⟨hx, lt_trans hxy hyp⟩
      have hyI : y ∈ Ico (0:ℝ) p.1.1 := ⟨by linarith, hyp⟩
      rw [hG p hp x hxI, hG p hp y hyI]
      exact p.2.2.1 hxI hyI hxy
    have hGsolve : ∀ u : ℝ, 0 ≤ u → (∃ p ∈ C, u < p.1.1) →
        SolvesEq5On c lam mu sigma cb ν G {u} := by
      intro u hu ⟨p, hp, hup⟩
      have hsp : SolvesEq5On c lam mu sigma cb ν p.1.2 {u} := fun v hv => by
        rw [mem_singleton_iff] at hv; subst hv; exact p.2.2.2 v ⟨hu, hup⟩
      refine solves_congr (fun v hv => by rw [mem_singleton_iff] at hv; rw [hv]; exact hu)
        (fun v hv z hz => ?_) hsp
      rw [mem_singleton_iff] at hv
      rw [hv] at hz
      exact (hG p hp z ⟨hz.1, lt_of_le_of_lt hz.2 hup⟩).symm
    by_cases hbd : BddAbove ((fun p : HSol c lam mu sigma cb ν => p.1.1) '' C)
    swap
    · exfalso
      rw [not_bddAbove_iff] at hbd
      have hcov : ∀ x : ℝ, ∃ p ∈ C, x < p.1.1 := by
        intro x
        obtain ⟨_, ⟨p, hp, rfl⟩, hxp⟩ := hbd x
        exact ⟨p, hp, hxp⟩
      refine hno ⟨G, fun x hx y hy hxy => hGanti x y hx hxy (hcov y), fun u hu => ?_⟩
      exact hGsolve u hu (hcov u) u (mem_singleton u)
    obtain ⟨p0, hp0⟩ := hCne
    have hTne : ((fun p : HSol c lam mu sigma cb ν => p.1.1) '' C).Nonempty :=
      ⟨p0.1.1, mem_image_of_mem _ hp0⟩
    obtain ⟨S, hSd⟩ : ∃ S : ℝ, S = sSup ((fun p : HSol c lam mu sigma cb ν => p.1.1) '' C) :=
      ⟨_, rfl⟩
    have hle : ∀ p ∈ C, p.1.1 ≤ S := fun p hp => by
      rw [hSd]; exact le_csSup hbd (mem_image_of_mem (fun p : HSol c lam mu sigma cb ν => p.1.1) hp)
    have hcov : ∀ x : ℝ, x < S → ∃ p ∈ C, x < p.1.1 := by
      intro x hx
      rw [hSd] at hx
      obtain ⟨_, ⟨p, hp, rfl⟩, hxp⟩ := exists_lt_of_lt_csSup hTne hx
      exact ⟨p, hp, hxp⟩
    have hS0 : 0 < S := lt_of_lt_of_le p0.2.1 (hle p0 hp0)
    refine ⟨⟨(S, G), hS0, fun x hx y hy hxy => hGanti x y hx.1 hxy (hcov y hy.2),
      fun u hu => hGsolve u hu.1 (hcov u hu.2) u (mem_singleton u)⟩, ?_⟩
    intro p hp
    exact ⟨hle p hp, fun x hx => (hG p hp x hx).symm⟩
  obtain ⟨M, hM⟩ := exists_maximal_of_chains_bounded hchain htrans
  obtain ⟨g', hanti, hsolve, hcont, hb, hpos, hden, hg'eq⟩ :=
    HS_close hc hlam hmu hsigma hcb hν hdens M.2.1 M.2.2.1 M.2.2.2
  obtain ⟨η, hη, h, hhA, hhS, hheq⟩ :=
    extend_step hc hlam hmu hsigma hcb hν M.2.1 hanti hsolve hcont hb hpos hden
  let q : HSol c lam mu sigma cb ν := ⟨(M.1.1 + η, h), by linarith [M.2.1],
    hhA.mono Ico_subset_Icc_self, fun u hu => hhS u (Ico_subset_Icc_self hu)⟩
  have hMq : HRel M q :=
    ⟨by show M.1.1 ≤ M.1.1 + η; linarith,
      fun x hx => ((hheq ⟨hx.1, hx.2.le⟩).trans (hg'eq hx)).symm⟩
  have := (hM q hMq).1
  have : M.1.1 + η ≤ M.1.1 := this
  linarith

end SchmidliRuinWork

open SchmidliRuin.Exist MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics in
theorem solution
    (c lam mu sigma : ℝ) (cb : ℝ → ℝ) (ν : Measure ℝ)
    (hc : 0 < c) (hlam : 0 < lam) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hcb : SchmidliRuin.Verif.ReinsPremium c cb) (hν : SchmidliRuin.Verif.ClaimLaw ν)
    (hdens : HasBoundedDensity ν) :
    (∃ g : ℝ → ℝ, StrictAntiOn g (Ici 0) ∧ SchmidliRuin.Verif.SolvesEq5On c lam mu sigma cb ν g (Ici 0)) ∧
    ∀ g₁ g₂ : ℝ → ℝ,
      StrictAntiOn g₁ (Ici 0) → SchmidliRuin.Verif.SolvesEq5On c lam mu sigma cb ν g₁ (Ici 0) →
      StrictAntiOn g₂ (Ici 0) → SchmidliRuin.Verif.SolvesEq5On c lam mu sigma cb ν g₂ (Ici 0) →
      EqOn g₁ g₂ (Ici 0) := by
  refine ⟨SchmidliRuinWork.existence hc hlam hmu hsigma hcb hν hdens, ?_⟩
  intro g₁ g₂ h1 hs1 h2 hs2
  exact SchmidliRuinWork.uniqueness hc hlam hmu hsigma hcb hν hdens h1 hs1 h2 hs2
