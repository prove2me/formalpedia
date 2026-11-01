-- Prove2me | solution 1 for RegretPricing.Structure.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T16:40:39.20906+00:00
-- url     : https://prove2.me/submissions/b581aba8-01e8-4109-a19c-25184c026f51

import Mathlib
import Definitions.Def_RegretPricing_Structure_Model

open RegretPricing.Structure MeasureTheory

section RPBasic

variable (D : WTP) (hD : D.Standing)
include hD

lemma rp_F_nonneg (x : ℝ) : 0 ≤ D.F x :=
  setIntegral_nonneg measurableSet_Iic (fun t _ => hD.2.2.1 t)

lemma rp_F_le_one (x : ℝ) : D.F x ≤ 1 := by
  have := setIntegral_le_integral (s := Set.Iic x) hD.2.2.2.2.1
    (Filter.Eventually.of_forall hD.2.2.1)
  unfold WTP.F; linarith [hD.2.2.2.2.2.1]

lemma rp_F_eq_one (x : ℝ) (hx : D.b ≤ x) : D.F x = 1 := by
  unfold WTP.F
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hD.2.2.2.2.2.1]
  intro t ht
  apply hD.2.2.2.1
  intro h; exact ht (Set.mem_Iic.2 (le_trans h.2 hx))

lemma rp_F_eq_zero (x : ℝ) (hx : x < D.a) : D.F x = 0 := by
  unfold WTP.F
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  apply hD.2.2.2.1
  intro h; exact absurd (lt_of_le_of_lt (le_trans h.1 ht) hx) (lt_irrefl _)

lemma rp_F_sub (y p : ℝ) : D.F p - D.F y = ∫ t in y..p, D.f t := by
  unfold WTP.F
  exact intervalIntegral.integral_Iic_sub_Iic hD.2.2.2.2.1.integrableOn
    hD.2.2.2.2.1.integrableOn

lemma rp_F_mono {y p : ℝ} (h : y ≤ p) : D.F y ≤ D.F p := by
  have := rp_F_sub D hD y p
  have h2 : 0 ≤ ∫ t in y..p, D.f t :=
    intervalIntegral.integral_nonneg h (fun t _ => hD.2.2.1 t)
  linarith

lemma rp_F_lip : ∃ M, 0 ≤ M ∧ ∀ y p, y ≤ p → D.F p - D.F y ≤ M * (p - y) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := D.a) (b := D.b)).exists_bound_of_continuousOn
    hD.2.2.2.2.2.2
  have hb : ∀ x, ‖D.f x‖ ≤ max C 0 := by
    intro x
    by_cases hx : x ∈ Set.Icc D.a D.b
    · exact le_trans (hC x hx) (le_max_left _ _)
    · rw [hD.2.2.2.1 x hx]; simp
  refine ⟨max C 0, le_max_right _ _, fun y p hyp => ?_⟩
  rw [rp_F_sub D hD y p]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := p)
    (f := D.f) (C := max C 0) (fun x _ => hb x)
  rw [abs_of_nonneg (by linarith)] at this
  exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using this)

lemma rp_Fbar_sub {y p : ℝ} (h : y ≤ p) : 0 ≤ D.Fbar y - D.Fbar p ∧ D.Fbar y - D.Fbar p ≤ 1 := by
  unfold WTP.Fbar
  have := rp_F_mono D hD h
  have := rp_F_nonneg D hD y
  have := rp_F_le_one D hD p
  constructor <;> linarith

lemma rp_Fbar_bds (y : ℝ) : 0 ≤ D.Fbar y ∧ D.Fbar y ≤ 1 := by
  unfold WTP.Fbar
  have := rp_F_nonneg D hD y
  have := rp_F_le_one D hD y
  constructor <;> linarith

lemma rp_rev_le (z : ℝ) (hz : z ≤ D.b) (y : ℝ) : revenue D y z ≤ D.b - z := by
  unfold revenue
  by_cases hy : D.b ≤ y
  · rw [WTP.Fbar, rp_F_eq_one D hD y hy]; simp; linarith
  · have hy' : y < D.b := lt_of_not_ge hy
    obtain ⟨h0, h1⟩ := rp_Fbar_bds D hD y
    by_cases hyz : z ≤ y
    · nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ y - z by linarith)]
    · nlinarith [mul_nonneg (show 0 ≤ z - y by linarith) h0]

lemma rp_ro_bdd (p z : ℝ) :
    BddAbove (Set.range fun y : {y : ℝ // y < p} => (y.1 - z) * (D.Fbar y.1 - D.Fbar p)) := by
  refine ⟨max (p - z) 0, ?_⟩
  rintro _ ⟨y, rfl⟩
  obtain ⟨h0, h1⟩ := rp_Fbar_sub D hD y.2.le
  have hy := y.2
  by_cases hyz : z ≤ y.1
  · have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ y.1 - z by linarith)
    simp only
    exact le_trans (by linarith) (le_max_left _ _)
  · have := mul_nonneg (show 0 ≤ z - y.1 by linarith) h0
    simp only
    exact le_trans (by nlinarith) (le_max_right _ _)

lemma rp_ro_nonneg (p z : ℝ) : 0 ≤ ro D p z := by
  unfold ro
  by_cases hpz : z < p
  · refine le_trans ?_ (le_ciSup (rp_ro_bdd D hD p z) ⟨(z + p) / 2, by linarith⟩)
    obtain ⟨h0, -⟩ := rp_Fbar_sub D hD (show (z + p) / 2 ≤ p by linarith)
    exact mul_nonneg (by linarith) h0
  · push Not at hpz
    obtain ⟨M, hM0, hM⟩ := rp_F_lip D hD
    by_contra hneg
    push Not at hneg
    set r := ⨆ y : {y : ℝ // y < p}, (y.1 - z) * (D.Fbar y.1 - D.Fbar p) with hr
    set ε := -r with hε
    have hεpos : 0 < ε := by linarith
    set K := (z - p + 1) * (M + 1) with hK
    have hKpos : 0 < K := by positivity
    set δ := min 1 (ε / (2 * K)) with hδ
    have hδpos : 0 < δ := lt_min one_pos (by positivity)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδ2 : δ ≤ ε / (2 * K) := min_le_right _ _
    have hle := le_ciSup (rp_ro_bdd D hD p z) ⟨p - δ, by linarith⟩
    simp only at hle
    have hFd : D.Fbar (p - δ) - D.Fbar p ≤ M * δ := by
      have := hM (p - δ) p (by linarith)
      unfold WTP.Fbar; linarith
    obtain ⟨h0, -⟩ := rp_Fbar_sub D hD (show p - δ ≤ p by linarith)
    have h3 : (z - (p - δ)) * (D.Fbar (p - δ) - D.Fbar p) ≤ (z - p + 1) * ((M + 1) * δ) :=
      mul_le_mul (by linarith) (by nlinarith) h0 (by linarith)
    have h4 : K * δ ≤ ε / 2 := by
      have := mul_le_mul_of_nonneg_left hδ2 hKpos.le
      rw [show K * (ε / (2 * K)) = ε / 2 by field_simp] at this
      exact this
    have : (z - p + 1) * ((M + 1) * δ) = K * δ := by rw [hK]; ring
    nlinarith

lemma rp_ro_anti (p : ℝ) {z z' : ℝ} (h : z ≤ z') : ro D p z' ≤ ro D p z := by
  unfold ro
  apply ciSup_mono (rp_ro_bdd D hD p z)
  intro y
  obtain ⟨h0, -⟩ := rp_Fbar_sub D hD y.2.le
  exact mul_le_mul_of_nonneg_right (by linarith) h0

lemma rp_S_bdd (p z : ℝ) (hz : z ≤ D.b) :
    BddAbove (Set.range fun y : {y : ℝ // p ≤ y} => revenue D y.1 z) :=
  ⟨D.b - z, by rintro _ ⟨y, rfl⟩; exact rp_rev_le D hD z hz y.1⟩

lemma rp_ru_nonneg (p z : ℝ) (hz : z ≤ D.b) : 0 ≤ ru D p z := by
  unfold ru
  have := le_ciSup (rp_S_bdd D hD p z hz) ⟨p, le_refl _⟩
  simp only at this
  linarith

lemma rp_ru_diff (p : ℝ) {z z' : ℝ} (h : z ≤ z') (hz' : z' ≤ D.b) :
    -(z' - z) ≤ ru D p z - ru D p z' := by
  unfold ru
  have hS : (⨆ y : {y : ℝ // p ≤ y}, revenue D y.1 z') ≤
      ⨆ y : {y : ℝ // p ≤ y}, revenue D y.1 z := by
    apply ciSup_mono (rp_S_bdd D hD p z (le_trans h hz'))
    intro y
    unfold revenue
    obtain ⟨h0, -⟩ := rp_Fbar_bds D hD y.1
    nlinarith [mul_nonneg (show 0 ≤ z' - z by linarith) h0]
  have : revenue D p z - revenue D p z' ≤ z' - z := by
    unfold revenue
    obtain ⟨h0, h1⟩ := rp_Fbar_bds D hD p
    nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ z' - z by linarith)]
  linarith

lemma rp_πhat_le (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (p z : ℝ) (hz : z ≤ D.b) :
    πhat D α β p z ≤ D.b - z := by
  unfold πhat
  have := rp_rev_le D hD z hz p
  nlinarith [mul_nonneg hα (rp_ro_nonneg D hD p z), mul_nonneg hβ (rp_ru_nonneg D hD p z hz)]

lemma rp_πhat_diff (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β ∧ β ≤ 1) (p : ℝ) {z z' : ℝ}
    (h : z ≤ z') (hz' : z' ≤ D.b) :
    πhat D α β p z ≤ πhat D α β p z' + 2 * (z' - z) := by
  unfold πhat
  have h1 : revenue D p z - revenue D p z' ≤ z' - z := by
    unfold revenue
    obtain ⟨h0, h1⟩ := rp_Fbar_bds D hD p
    nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ z' - z by linarith)]
  have h2 := rp_ro_anti D hD p h
  have h3 := rp_ru_diff D hD p h hz'
  nlinarith [mul_le_mul_of_nonneg_left h2 hα, mul_le_mul_of_nonneg_left h3 hβ.1]

lemma rp_V_le (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (z : ℝ) (hz : z ≤ D.b) :
    regretValue D α β z ≤ D.b - z :=
  ciSup_le fun p => rp_πhat_le D hD α β hα hβ p z hz

lemma rp_V_ge (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (z : ℝ) (hz : z ≤ D.b) (p : ℝ) :
    πhat D α β p z ≤ regretValue D α β z :=
  le_ciSup (f := fun p => πhat D α β p z)
    ⟨D.b - z, by rintro _ ⟨q, rfl⟩; exact rp_πhat_le D hD α β hα hβ q z hz⟩ p

lemma rp_V_lip (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β ∧ β ≤ 1) {z z' : ℝ} (h : z ≤ z')
    (hz' : z' ≤ D.b) :
    regretValue D α β z ≤ regretValue D α β z' + 2 * (z' - z) := by
  apply ciSup_le
  intro p
  have := rp_πhat_diff D hD α β hα hβ p h hz'
  have := rp_V_ge D hD α β hα hβ.1 z' hz' p
  linarith

lemma rp_V_b_nonneg (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) : 0 ≤ regretValue D α β D.b := by
  refine le_trans ?_ (rp_V_ge D hD α β hα hβ D.b le_rfl D.b)
  have hro : ro D D.b D.b ≤ 0 := by
    unfold ro
    haveI : Nonempty {y : ℝ // y < D.b} := ⟨⟨D.b - 1, by linarith⟩⟩
    apply ciSup_le
    intro y
    obtain ⟨h0, -⟩ := rp_Fbar_sub D hD y.2.le
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [y.2]) h0
  have hru : ru D D.b D.b ≤ 0 := by
    unfold ru
    haveI : Nonempty {y : ℝ // D.b ≤ y} := ⟨⟨D.b, le_rfl⟩⟩
    have : (⨆ y : {y : ℝ // D.b ≤ y}, revenue D y.1 D.b) ≤ 0 := by
      apply ciSup_le
      intro y
      unfold revenue WTP.Fbar
      rw [rp_F_eq_one D hD y.1 y.2]; simp
    have : revenue D D.b D.b = 0 := by unfold revenue; simp
    linarith
  unfold πhat
  have : revenue D D.b D.b = 0 := by unfold revenue; simp
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hα hro, mul_nonpos_of_nonneg_of_nonpos hβ hru]

end RPBasic

section RPIFR

variable (D : WTP) (hD : D.Standing)
include hD

lemma rp_F_eq_prim : D.F = fun x => D.F 0 + ∫ t in (0:ℝ)..x, D.f t := by
  funext x; have := rp_F_sub D hD 0 x; linarith

lemma rp_F_cont : Continuous D.F := by
  rw [rp_F_eq_prim D hD]
  exact continuous_const.add
    (intervalIntegral.continuous_primitive (fun _ _ => hD.2.2.2.2.1.intervalIntegrable) 0)

lemma rp_Fbar_cont : Continuous D.Fbar := by
  have : D.Fbar = fun x => 1 - D.F x := rfl
  rw [this]; exact continuous_const.sub (rp_F_cont D hD)

lemma rp_F_a : D.F D.a = 0 := by
  obtain ⟨M, hM0, hM⟩ := rp_F_lip D hD
  have h0 := rp_F_nonneg D hD D.a
  refine le_antisymm ?_ h0
  by_contra hcon
  push Not at hcon
  set ε := D.F D.a with hε
  have hδ : 0 < ε / (2 * (M + 1)) := by positivity
  have := hM (D.a - ε / (2 * (M + 1))) D.a (by linarith)
  rw [rp_F_eq_zero D hD (D.a - ε / (2 * (M + 1))) (by linarith)] at this
  have h2 : M * (D.a - (D.a - ε / (2 * (M + 1)))) ≤ ε / 2 := by
    rw [show D.a - (D.a - ε / (2 * (M + 1))) = ε / (2 * (M + 1)) by ring]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

lemma rp_Fbar_le_a (x : ℝ) (hx : x ≤ D.a) : D.Fbar x = 1 := by
  have h1 := rp_F_mono D hD hx
  have h2 := rp_F_nonneg D hD x
  rw [rp_F_a D hD] at h1
  unfold WTP.Fbar; linarith

lemma rp_F_deriv (p : ℝ) (hp : p ∈ Set.Ioo D.a D.b) : HasDerivAt D.F (D.f p) p := by
  have hc : ContinuousAt D.f p := hD.2.2.2.2.2.2.continuousAt (Icc_mem_nhds hp.1 hp.2)
  have hmeas : StronglyMeasurableAtFilter D.f (nhds p) :=
    (hD.2.2.2.2.2.2.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo p hp
  have h := intervalIntegral.integral_hasDerivAt_right (a := 0)
    hD.2.2.2.2.1.intervalIntegrable hmeas hc
  rw [rp_F_eq_prim D hD]
  exact h.const_add _

lemma rp_Fbar_deriv (p : ℝ) (hp : p ∈ Set.Ioo D.a D.b) : HasDerivAt D.Fbar (-D.f p) p := by
  have : D.Fbar = fun x => 1 - D.F x := rfl
  rw [this]; exact (rp_F_deriv D hD p hp).const_sub 1

lemma rp_Fbar_pos (hIFR : D.IFR) (x : ℝ) (hx : x < D.b) : 0 < D.Fbar x := by
  by_contra hcon
  push Not at hcon
  have hx0 : D.Fbar x = 0 := le_antisymm hcon (rp_Fbar_bds D hD x).1
  have hxa : D.a < x := by
    by_contra h; push Not at h; rw [rp_Fbar_le_a D hD x h] at hx0; norm_num at hx0
  have hz : ∀ p ∈ Set.Ioo D.a D.b, D.f p = 0 := by
    intro p hp
    by_cases hpos : 0 < D.Fbar p
    · have hpx : p < x := by
        by_contra h; push Not at h
        have := (rp_Fbar_sub D hD h).1
        linarith
      have := hIFR (show p ∈ Set.Iio D.b from hp.2) (show x ∈ Set.Iio D.b from hx) hpx.le
      unfold WTP.h at this
      rw [hx0, div_zero, div_le_iff₀ hpos, zero_mul] at this
      exact le_antisymm this (hD.2.2.1 p)
    · have hp0 : D.Fbar p = 0 := le_antisymm (not_lt.1 hpos) (rp_Fbar_bds D hD p).1
      have hF1 : ∀ y ∈ Set.Ici p, D.F y = D.F p := by
        intro y hy
        have h1 := rp_F_mono D hD (show p ≤ y from hy)
        have h2 := rp_F_le_one D hD y
        unfold WTP.Fbar at hp0
        linarith
      have hd1 : HasDerivWithinAt D.F (D.f p) (Set.Ici p) p :=
        (rp_F_deriv D hD p hp).hasDerivWithinAt
      have hd2 : HasDerivWithinAt D.F 0 (Set.Ici p) p :=
        (hasDerivWithinAt_const p (Set.Ici p) (D.F p)).congr hF1 rfl
      exact (uniqueDiffWithinAt_Ici p).eq_deriv _ hd1 hd2
  have hint : ∫ t in D.a..D.b, D.f t = 0 := by
    rw [intervalIntegral.integral_of_le hD.2.1.le, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_eq_zero_of_forall_eq_zero hz
  have := rp_F_sub D hD D.a D.b
  rw [rp_F_a D hD, rp_F_eq_one D hD D.b le_rfl, hint] at this
  norm_num at this

lemma rp_logFbar_concave (hIFR : D.IFR) :
    ConcaveOn ℝ (Set.Ico D.a D.b) (fun x => Real.log (D.Fbar x)) := by
  have hderiv : ∀ p ∈ Set.Ioo D.a D.b,
      HasDerivAt (fun x => Real.log (D.Fbar x)) (-D.f p / D.Fbar p) p := fun p hp =>
    (rp_Fbar_deriv D hD p hp).log (ne_of_gt (rp_Fbar_pos D hD hIFR p hp.2))
  apply AntitoneOn.concaveOn_of_deriv (convex_Ico _ _)
  · exact ((rp_Fbar_cont D hD).continuousOn).log
      (fun x hx => ne_of_gt (rp_Fbar_pos D hD hIFR x hx.2))
  · rw [interior_Ico]
    exact fun p hp => (hderiv p hp).differentiableAt.differentiableWithinAt
  · rw [interior_Ico]
    intro p hp q hq hpq
    rw [(hderiv p hp).deriv, (hderiv q hq).deriv]
    have := hIFR (show p ∈ Set.Iio D.b from hp.2) (show q ∈ Set.Iio D.b from hq.2) hpq
    unfold WTP.h at this
    rw [neg_div, neg_div]
    exact neg_le_neg this

lemma rp_logsub_strictConcave (z : ℝ) :
    StrictConcaveOn ℝ (Set.Ioi z) (fun p => Real.log (p - z)) := by
  refine ⟨convex_Ioi z, fun x hx y hy hxy u v hu hv huv => ?_⟩
  have := strictConcaveOn_log_Ioi.2 (show x - z ∈ Set.Ioi (0:ℝ) from Set.mem_Ioi.2 (sub_pos.2 hx))
    (show y - z ∈ Set.Ioi (0:ℝ) from Set.mem_Ioi.2 (sub_pos.2 hy)) (by intro h; apply hxy; linarith) hu hv huv
  simp only [smul_eq_mul] at this ⊢
  have e : u * x + v * y - z = u * (x - z) + v * (y - z) := by
    have : z = (u + v) * z := by rw [huv, one_mul]
    nth_rewrite 1 [this]; ring
  rw [e]; exact this

/-- Strict quasi-concavity of `π(·, z)` on `(z, b)`. -/
lemma rp_rev_sqc (hIFR : D.IFR) (z x m y : ℝ) (hzx : z < x) (hxm : x < m) (hmy : m < y)
    (hyb : y < D.b) : min (revenue D x z) (revenue D y z) < revenue D m z := by
  by_cases hma : m ≤ D.a
  · have h1 : revenue D x z < revenue D m z := by
      unfold revenue
      rw [rp_Fbar_le_a D hD x (by linarith), rp_Fbar_le_a D hD m hma]; linarith
    exact lt_of_le_of_lt (min_le_left _ _) h1
  push Not at hma
  set x' := max x D.a with hx'
  have hxx' : revenue D x z ≤ revenue D x' z := by
    by_cases hxa : D.a ≤ x
    · rw [hx', max_eq_left hxa]
    · push Not at hxa
      rw [hx', max_eq_right hxa.le]
      unfold revenue
      rw [rp_Fbar_le_a D hD x hxa.le, rp_Fbar_le_a D hD D.a le_rfl]; linarith
  have hx'm : x' < m := max_lt hxm hma
  set S := Set.Ico D.a D.b ∩ Set.Ioi z with hS
  have hL : StrictConcaveOn ℝ S (fun p => Real.log (p - z) + Real.log (D.Fbar p)) :=
    ((rp_logsub_strictConcave D hD z).subset Set.inter_subset_right
      ((convex_Ico _ _).inter (convex_Ioi z))).add_concaveOn
      ((rp_logFbar_concave D hD hIFR).subset Set.inter_subset_left
      ((convex_Ico _ _).inter (convex_Ioi z)))
  have hx'S : x' ∈ S := ⟨⟨le_max_right _ _, max_lt (by linarith) hD.2.1⟩, lt_of_lt_of_le hzx (le_max_left _ _)⟩
  have hyS : y ∈ S := ⟨⟨(by linarith : D.a ≤ y), hyb⟩, (show z < y by linarith)⟩
  have hseg : m ∈ openSegment ℝ x' y := by
    rw [openSegment_eq_Ioo (by linarith)]; exact ⟨hx'm, hmy⟩
  have key := hL.lt_on_openSegment hx'S hyS (by intro h; linarith) hseg
  have hexp : ∀ p ∈ S, revenue D p z = Real.exp (Real.log (p - z) + Real.log (D.Fbar p)) := by
    intro p hp
    rw [Real.exp_add, Real.exp_log (sub_pos.2 hp.2),
      Real.exp_log (rp_Fbar_pos D hD hIFR p hp.1.2)]
    rfl
  have hmS : m ∈ S := ⟨⟨hma.le, (by linarith : m < D.b)⟩, (show z < m by linarith)⟩
  have : min (revenue D x' z) (revenue D y z) < revenue D m z := by
    rw [hexp x' hx'S, hexp y hyS, hexp m hmS]
    rcases min_choice (Real.log (x' - z) + Real.log (D.Fbar x'))
      (Real.log (y - z) + Real.log (D.Fbar y)) with h | h
    · rw [h] at key
      calc min _ _ ≤ Real.exp (Real.log (x' - z) + Real.log (D.Fbar x')) := min_le_left _ _
        _ < _ := Real.exp_lt_exp.2 key
    · rw [h] at key
      calc min _ _ ≤ Real.exp (Real.log (y - z) + Real.log (D.Fbar y)) := min_le_right _ _
        _ < _ := Real.exp_lt_exp.2 key
  exact lt_of_le_of_lt (min_le_min_right _ hxx') this

lemma rp_rev_pos (hIFR : D.IFR) (z m : ℝ) (hzm : z < m) (hmb : m < D.b) : 0 < revenue D m z :=
  mul_pos (by linarith) (rp_Fbar_pos D hD hIFR m hmb)

lemma rp_rev_ge_b (z m : ℝ) (hm : D.b ≤ m) : revenue D m z = 0 := by
  unfold revenue WTP.Fbar; rw [rp_F_eq_one D hD m hm]; ring

/-- Quasi-concavity of `π(·, z)` on `ℝ`. -/
lemma rp_rev_qc (hIFR : D.IFR) (z x m y : ℝ) (hz : z < D.b) (hxm : x < m) (hmy : m < y) :
    min (revenue D x z) (revenue D y z) ≤ revenue D m z := by
  by_cases hmz : m ≤ z
  · refine le_trans (min_le_left _ _) ?_
    unfold revenue
    obtain ⟨h1, h2⟩ := rp_Fbar_sub D hD hxm.le
    have h3 := (rp_Fbar_bds D hD m).1
    nlinarith [mul_le_mul_of_nonpos_left (show D.Fbar m ≤ D.Fbar x by linarith)
      (show x - z ≤ 0 by linarith)]
  push Not at hmz
  by_cases hmb : D.b ≤ m
  · rw [rp_rev_ge_b D hD z m hmb]
    exact le_trans (min_le_right _ _) (le_of_eq (rp_rev_ge_b D hD z y (by linarith)))
  push Not at hmb
  have hpos := rp_rev_pos D hD hIFR z m hmz hmb
  by_cases hxz : x ≤ z
  · refine le_trans (min_le_left _ _) ?_
    unfold revenue at hpos ⊢
    have := (rp_Fbar_bds D hD x).1
    nlinarith [mul_nonneg (show 0 ≤ z - x by linarith) this]
  push Not at hxz
  by_cases hyb : D.b ≤ y
  · rw [rp_rev_ge_b D hD z y hyb]; exact le_trans (min_le_right _ _) hpos.le
  push Not at hyb
  exact (rp_rev_sqc D hD hIFR z x m y hxz hxm hmy hyb).le

end RPIFR

section RPLemma1

variable (D : WTP) (hD : D.Standing)
include hD

lemma rp_ro_mono (z : ℝ) : Monotone (fun p => ro D p z) := by
  intro p q hpq
  simp only
  unfold ro
  haveI : Nonempty {y : ℝ // y < p} := ⟨⟨p - 1, by linarith⟩⟩
  apply ciSup_le
  intro y
  by_cases hyz : z ≤ y.1
  · have h1 : (y.1 - z) * (D.Fbar y.1 - D.Fbar p) ≤ (y.1 - z) * (D.Fbar y.1 - D.Fbar q) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      have := (rp_Fbar_sub D hD hpq).1
      linarith
    exact le_trans h1 (le_ciSup (f := fun y : {y : ℝ // y < q} =>
      (y.1 - z) * (D.Fbar y.1 - D.Fbar q)) (rp_ro_bdd D hD q z)
      ⟨y.1, lt_of_lt_of_le y.2 hpq⟩)
  · push Not at hyz
    have h0 := (rp_Fbar_sub D hD y.2.le).1
    have : (y.1 - z) * (D.Fbar y.1 - D.Fbar p) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) h0
    exact le_trans this (rp_ro_nonneg D hD q z)

/-- Unimodality of `π(·, z)` around a maximizer, for `z ∈ [0, b]`. -/
lemma rp_unimodal (hIFR : D.IFR) (z : ℝ) (hz : z ≤ D.b) (p : ℝ) (hp : IsUnbiasedPrice D z p) :
    MonotoneOn (fun q => revenue D q z) (Set.Iic p) ∧
      AntitoneOn (fun q => revenue D q z) (Set.Ici p) := by
  rcases lt_or_eq_of_le hz with hz | hz
  · constructor
    · intro x hx y hy hxy
      simp only
      rcases eq_or_lt_of_le hxy with h | h
      · rw [h]
      rcases eq_or_lt_of_le (show y ≤ p from hy) with h' | h'
      · rw [h']; exact hp x
      have := rp_rev_qc D hD hIFR z x y p hz h h'
      rwa [min_eq_left (hp x)] at this
    · intro x hx y hy hxy
      simp only
      rcases eq_or_lt_of_le hxy with h | h
      · rw [h]
      rcases eq_or_lt_of_le (show p ≤ x from hx) with h' | h'
      · rw [← h']; exact hp y
      have := rp_rev_qc D hD hIFR z p x y hz h' h
      rwa [min_eq_right (hp y)] at this
  · -- z = b : π(·, b) is monotone on ℝ
    have hmono : Monotone (fun q => revenue D q z) := by
      intro x y hxy
      simp only
      by_cases hyb : D.b ≤ y
      · rw [rp_rev_ge_b D hD z y hyb]
        unfold revenue
        by_cases hxb : D.b ≤ x
        · rw [WTP.Fbar, rp_F_eq_one D hD x hxb]; simp
        · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (rp_Fbar_bds D hD x).1
      · push Not at hyb
        unfold revenue
        obtain ⟨h1, -⟩ := rp_Fbar_sub D hD hxy
        have h3 := (rp_Fbar_bds D hD y).1
        nlinarith [mul_le_mul_of_nonpos_left (show D.Fbar y ≤ D.Fbar x by linarith)
          (show x - z ≤ 0 by linarith)]
    constructor
    · exact fun x _ y _ h => hmono h
    · intro x hx y hy hxy
      have e1 : revenue D x z = revenue D p z := le_antisymm (hp x) (hmono hx)
      have e2 : revenue D y z = revenue D p z := le_antisymm (hp y) (hmono hy)
      simp only; rw [e1, e2]


lemma rp_unbiased_gen (hIFR : D.IFR) (z : ℝ)
    (hz : True ∧ z < D.b) :
    (∃! p, IsUnbiasedPrice D z p) ∧
      ∀ p, IsUnbiasedPrice D z p →
        MonotoneOn (fun q => revenue D q z) (Set.Iic p) ∧
          AntitoneOn (fun q => revenue D q z) (Set.Ici p) := by
  have hcont : Continuous (fun q => revenue D q z) := by
    unfold revenue; exact (continuous_id.sub continuous_const).mul (rp_Fbar_cont D hD)
  have hunimod : ∀ p, IsUnbiasedPrice D z p →
      MonotoneOn (fun q => revenue D q z) (Set.Iic p) ∧
        AntitoneOn (fun q => revenue D q z) (Set.Ici p) := by
    intro p hp
    constructor
    · intro x hx y hy hxy
      simp only
      rcases eq_or_lt_of_le hxy with h | h
      · rw [h]
      rcases eq_or_lt_of_le (show y ≤ p from hy) with h' | h'
      · rw [h']; exact hp x
      have := rp_rev_qc D hD hIFR z x y p hz.2 h h'
      rwa [min_eq_left (hp x)] at this
    · intro x hx y hy hxy
      simp only
      rcases eq_or_lt_of_le hxy with h | h
      · rw [h]
      rcases eq_or_lt_of_le (show p ≤ x from hx) with h' | h'
      · rw [← h']; exact hp y
      have := rp_rev_qc D hD hIFR z p x y hz.2 h' h
      rwa [min_eq_right (hp y)] at this
  refine ⟨?_, hunimod⟩
  obtain ⟨p0, hp0, hmax⟩ := (isCompact_Icc (a := z) (b := D.b)).exists_isMaxOn
    (Set.nonempty_Icc.2 hz.2.le) hcont.continuousOn
  have hb0 : revenue D D.b z = 0 := rp_rev_ge_b D hD z D.b le_rfl
  have hp0nn : 0 ≤ revenue D p0 z := by
    have := hmax (show D.b ∈ Set.Icc z D.b from ⟨hz.2.le, le_rfl⟩)
    simp only [Set.mem_setOf_eq] at this; linarith
  have hp0max : IsUnbiasedPrice D z p0 := by
    intro q
    by_cases hqz : q < z
    · refine le_trans ?_ hp0nn
      unfold revenue
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (rp_Fbar_bds D hD q).1
    by_cases hqb : D.b < q
    · rw [rp_rev_ge_b D hD z q hqb.le]; exact hp0nn
    exact hmax ⟨not_lt.1 hqz, not_lt.1 hqb⟩
  refine ⟨p0, hp0max, ?_⟩
  -- uniqueness
  have hpos : ∀ p, IsUnbiasedPrice D z p → z < p ∧ p < D.b ∧ 0 < revenue D p z := by
    intro p hp
    have h1 := rp_rev_pos D hD hIFR z ((z + D.b) / 2) (by linarith) (by linarith)
    have h2 := hp ((z + D.b) / 2)
    have hr : 0 < revenue D p z := by linarith
    refine ⟨?_, ?_, hr⟩
    · by_contra h; push Not at h
      unfold revenue at hr
      have := mul_nonpos_of_nonpos_of_nonneg (show p - z ≤ 0 by linarith) (rp_Fbar_bds D hD p).1
      linarith
    · by_contra h; push Not at h
      rw [rp_rev_ge_b D hD z p h] at hr; exact lt_irrefl _ hr
  have key : ∀ p1 p2, IsUnbiasedPrice D z p1 → IsUnbiasedPrice D z p2 → ¬ p1 < p2 := by
    intro p1 p2 h1 h2 hlt
    obtain ⟨hz1, -, -⟩ := hpos p1 h1
    obtain ⟨-, hb2, -⟩ := hpos p2 h2
    have := rp_rev_sqc D hD hIFR z p1 ((p1 + p2) / 2) p2 hz1 (by linarith) (by linarith) hb2
    rw [min_eq_left (h2 p1)] at this
    linarith [h1 ((p1 + p2) / 2)]
  intro q hq
  rcases lt_trichotomy q p0 with h | h | h
  · exact absurd h (key q p0 hq hp0max)
  · exact h
  · exact absurd h (key p0 q hp0max hq)


lemma rp_unbiased (hIFR : D.IFR) (z : ℝ)
    (hz : 0 ≤ z ∧ z < D.b) :
    (∃! p, IsUnbiasedPrice D z p) ∧
      ∀ p, IsUnbiasedPrice D z p →
        MonotoneOn (fun q => revenue D q z) (Set.Iic p) ∧
          AntitoneOn (fun q => revenue D q z) (Set.Ici p) :=
  rp_unbiased_gen D hD hIFR z ⟨trivial, hz.2⟩

lemma rp_lemma1 (hIFR : D.IFR) (z : ℝ)
    (hz : 0 ≤ z ∧ z ≤ D.b) (pstar : ℝ) (hpstar : IsUnbiasedPrice D z pstar) :
    Monotone (fun p => ro D p z) ∧ Antitone (fun p => ru D p z) ∧
      ∀ p, pstar ≤ p → ru D p z = 0 := by
  obtain ⟨hmo, han⟩ := rp_unimodal D hD hIFR z hz.2 pstar hpstar
  have hbdd : ∀ p, BddAbove (Set.range fun y : {y : ℝ // p ≤ y} => revenue D y.1 z) :=
    fun p => ⟨revenue D pstar z, by rintro _ ⟨y, rfl⟩; exact hpstar y.1⟩
  have hSlo : ∀ p, p ≤ pstar → (⨆ y : {y : ℝ // p ≤ y}, revenue D y.1 z) = revenue D pstar z := by
    intro p hp
    haveI : Nonempty {y : ℝ // p ≤ y} := ⟨⟨p, le_rfl⟩⟩
    exact le_antisymm (ciSup_le fun y => hpstar y.1)
      (le_ciSup (f := fun y : {y : ℝ // p ≤ y} => revenue D y.1 z) (hbdd p) ⟨pstar, hp⟩)
  have hShi : ∀ p, pstar ≤ p → ru D p z = 0 := by
    intro p hp
    unfold ru
    haveI : Nonempty {y : ℝ // p ≤ y} := ⟨⟨p, le_rfl⟩⟩
    have : (⨆ y : {y : ℝ // p ≤ y}, revenue D y.1 z) = revenue D p z :=
      le_antisymm (ciSup_le fun y => han hp (le_trans hp y.2) y.2)
        (le_ciSup (f := fun y : {y : ℝ // p ≤ y} => revenue D y.1 z) (hbdd p) ⟨p, le_rfl⟩)
    rw [this]; ring
  have hru0 : ∀ p, 0 ≤ ru D p z := by
    intro p
    unfold ru
    have := le_ciSup (f := fun y : {y : ℝ // p ≤ y} => revenue D y.1 z) (hbdd p) ⟨p, le_rfl⟩
    simp only at this; linarith
  refine ⟨rp_ro_mono D hD z, ?_, hShi⟩
  intro p q hpq
  simp only
  by_cases hq : pstar ≤ q
  · rw [hShi q hq]; exact hru0 p
  · push Not at hq
    unfold ru
    rw [hSlo p (by linarith), hSlo q hq.le]
    have := hmo (show p ∈ Set.Iic pstar by simp; linarith) (show q ∈ Set.Iic pstar from hq.le) hpq
    simp only at this; linarith


lemma rp_πstar_eq (z : ℝ) (pstar : ℝ) (hpstar : IsUnbiasedPrice D z pstar) :
    πstar D z = revenue D pstar z :=
  le_antisymm (ciSup_le hpstar)
    (le_ciSup (f := fun p => revenue D p z) ⟨revenue D pstar z, by rintro _ ⟨y, rfl⟩; exact hpstar y⟩ pstar)

lemma rp_eq15 (hIFR : D.IFR) (α β : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1) (z : ℝ) (hz : 0 ≤ z ∧ z < D.b)
    (pstar : ℝ) (hpstar : IsUnbiasedPrice D z pstar) :
    (∀ p, p ≤ pstar →
        πhat D α β p z = (1 + β) * revenue D p z - α * ro D p z - β * πstar D z) ∧
      regretValue D α β z =
        ⨆ p : ℝ, ((1 + β) * revenue D p z - α * ro D p z - β * πstar D z) := by
  obtain ⟨hro, hru, hru0⟩ := rp_lemma1 D hD hIFR z ⟨hz.1, hz.2.le⟩ pstar hpstar
  have hps := rp_πstar_eq D hD z pstar hpstar
  have hbdd : ∀ p, BddAbove (Set.range fun y : {y : ℝ // p ≤ y} => revenue D y.1 z) :=
    fun p => ⟨revenue D pstar z, by rintro _ ⟨y, rfl⟩; exact hpstar y.1⟩
  have hlo : ∀ p, p ≤ pstar →
      πhat D α β p z = (1 + β) * revenue D p z - α * ro D p z - β * πstar D z := by
    intro p hp
    have hS : (⨆ y : {y : ℝ // p ≤ y}, revenue D y.1 z) = revenue D pstar z := by
      haveI : Nonempty {y : ℝ // p ≤ y} := ⟨⟨p, le_rfl⟩⟩
      exact le_antisymm (ciSup_le fun y => hpstar y.1)
        (le_ciSup (f := fun y : {y : ℝ // p ≤ y} => revenue D y.1 z) (hbdd p) ⟨pstar, hp⟩)
    unfold πhat ru; rw [hS, hps]; ring
  refine ⟨hlo, ?_⟩
  set G := fun p => (1 + β) * revenue D p z - α * ro D p z - β * πstar D z with hG
  have hGle : ∀ p, G p ≤ πhat D α β p z := by
    intro p
    by_cases hp : p ≤ pstar
    · rw [hlo p hp]
    · push Not at hp
      simp only [hG]
      unfold πhat
      rw [hru0 p hp.le, hps]
      have := hpstar p
      nlinarith [mul_le_mul_of_nonneg_left this hβ.1]
  have hhi : ∀ p, pstar < p → πhat D α β p z ≤ G pstar := by
    intro p hp
    show πhat D α β p z ≤ (1 + β) * revenue D pstar z - α * ro D pstar z - β * πstar D z
    rw [← hlo pstar le_rfl]
    unfold πhat
    rw [hru0 p hp.le, hru0 pstar le_rfl]
    have h1 := hpstar p
    have h2 := hro hp.le
    simp only at h2
    nlinarith [mul_le_mul_of_nonneg_left h2 hα.1]
  have hVb : BddAbove (Set.range fun p => πhat D α β p z) :=
    ⟨D.b - z, by rintro _ ⟨q, rfl⟩; exact rp_πhat_le D hD α β hα.1 hβ.1 q z hz.2.le⟩
  have hGb : BddAbove (Set.range G) :=
    ⟨D.b - z, by rintro _ ⟨q, rfl⟩; exact le_trans (hGle q) (rp_πhat_le D hD α β hα.1 hβ.1 q z hz.2.le)⟩
  apply le_antisymm
  · apply ciSup_le
    intro p
    by_cases hp : p ≤ pstar
    · rw [hlo p hp]; exact le_ciSup hGb p
    · exact le_trans (hhi p (lt_of_not_ge hp)) (le_ciSup hGb pstar)
  · exact ciSup_le fun p => le_trans (hGle p) (le_ciSup hVb p)

lemma rp_prop2 (hIFR : D.IFR) (α β : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1) (z : ℝ) (hz : 0 ≤ z ∧ z < D.b)
    (phat pstar : ℝ) (hphat : IsRegretPrice D α β z phat) (hpstar : IsUnbiasedPrice D z pstar) :
    phat ≤ pstar := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hro, hru, hru0⟩ := rp_lemma1 D hD hIFR z ⟨hz.1, hz.2.le⟩ pstar hpstar
  obtain ⟨⟨q, hq, huniq⟩, -⟩ := rp_unbiased D hD hIFR z hz
  have hlt : revenue D phat z < revenue D pstar z := by
    rcases lt_or_eq_of_le (hpstar phat) with h | h
    · exact h
    · exfalso
      have h1 : IsUnbiasedPrice D z phat := fun p' => h ▸ hpstar p'
      have := (huniq phat h1).trans (huniq pstar hpstar).symm
      linarith
  have := hphat pstar
  unfold πhat at this
  rw [hru0 phat hcon.le, hru0 pstar le_rfl] at this
  have h2 := hro hcon.le
  simp only at h2
  nlinarith [mul_le_mul_of_nonneg_left h2 hα.1]

end RPLemma1

section RPProp1

variable (D : WTP) (hD : D.Standing)
include hD

lemma rp_T_le_ro (p z y : ℝ) (hy : z ≤ y) :
    (y - z) * (D.Fbar y - D.Fbar p) ≤ ro D p z := by
  by_cases hyp : y < p
  · exact le_ciSup (f := fun y : {y : ℝ // y < p} => (y.1 - z) * (D.Fbar y.1 - D.Fbar p))
      (rp_ro_bdd D hD p z) ⟨y, hyp⟩
  · push Not at hyp
    obtain ⟨h0, -⟩ := rp_Fbar_sub D hD hyp
    have : (y - z) * (D.Fbar y - D.Fbar p) ≤ 0 := by
      have : D.Fbar y - D.Fbar p ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) this
    exact le_trans this (rp_ro_nonneg D hD p z)

lemma rp_ro_attain' (z p : ℝ) (hz : z < D.b) :
    ∃ y, z ≤ y ∧ y ≤ D.b ∧ (z < p → y ≤ p) ∧ ro D p z = (y - z) * (D.Fbar y - D.Fbar p) := by
  by_cases hpz : p ≤ z
  · refine ⟨z, le_rfl, hz.le, fun h => absurd h (not_lt.2 hpz), ?_⟩
    simp only [sub_self, zero_mul]
    apply le_antisymm _ (rp_ro_nonneg D hD p z)
    unfold ro
    haveI : Nonempty {y : ℝ // y < p} := ⟨⟨p - 1, by linarith⟩⟩
    apply ciSup_le
    intro y
    obtain ⟨h0, -⟩ := rp_Fbar_sub D hD y.2.le
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [y.2]) h0
  push Not at hpz
  set q := min p D.b with hq
  have hzq : z ≤ q := le_min hpz.le hz.le
  have hcT : ContinuousOn (fun y => (y - z) * (D.Fbar y - D.Fbar p)) (Set.Icc z q) :=
    ((continuous_id.sub continuous_const).mul
      ((rp_Fbar_cont D hD).sub continuous_const)).continuousOn
  obtain ⟨y0, hy0, hmax⟩ := (isCompact_Icc (a := z) (b := q)).exists_isMaxOn
    (Set.nonempty_Icc.2 hzq) hcT
  refine ⟨y0, hy0.1, le_trans hy0.2 (min_le_right _ _), fun _ => le_trans hy0.2 (min_le_left _ _), ?_⟩
  have hz0 : (z - z) * (D.Fbar z - D.Fbar p) ≤ (y0 - z) * (D.Fbar y0 - D.Fbar p) :=
    hmax ⟨le_rfl, hzq⟩
  simp only [sub_self, zero_mul] at hz0
  apply le_antisymm
  · unfold ro
    haveI : Nonempty {y : ℝ // y < p} := ⟨⟨p - 1, by linarith⟩⟩
    apply ciSup_le
    intro y
    by_cases hyz : y.1 < z
    · obtain ⟨h0, -⟩ := rp_Fbar_sub D hD y.2.le
      exact le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) h0) hz0
    push Not at hyz
    by_cases hyq : y.1 ≤ q
    · exact hmax ⟨hyz, hyq⟩
    · push Not at hyq
      have hpb : D.b < p := by
        by_contra h; push Not at h
        have : q = p := min_eq_left h
        have := y.2; linarith
      have hqb : q = D.b := min_eq_right hpb.le
      have e1 : D.Fbar y.1 = 0 := by
        unfold WTP.Fbar; rw [rp_F_eq_one D hD _ (by linarith)]; ring
      have e2 : D.Fbar p = 0 := by
        unfold WTP.Fbar; rw [rp_F_eq_one D hD _ (by linarith [y.2])]; ring
      have : (y.1 - z) * (D.Fbar y.1 - D.Fbar p) = 0 := by rw [e1, e2]; ring
      rw [this]; exact hz0
  · exact rp_T_le_ro D hD p z y0 hy0.1

lemma rp_ro_attain (z p : ℝ) (hz : z < D.b) :
    ∃ y, z ≤ y ∧ y ≤ D.b ∧ ro D p z = (y - z) * (D.Fbar y - D.Fbar p) := by
  obtain ⟨y, h1, h2, -, h4⟩ := rp_ro_attain' D hD z p hz
  exact ⟨y, h1, h2, h4⟩

lemma rp_Fbar_abs (M : ℝ) (hM : ∀ y p, y ≤ p → D.F p - D.F y ≤ M * (p - y)) (p q : ℝ) :
    |D.Fbar p - D.Fbar q| ≤ M * |p - q| := by
  unfold WTP.Fbar
  rcases le_total p q with h | h
  · have h1 := hM p q h; have h2 := rp_F_mono D hD h
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have h1 := hM q p h; have h2 := rp_F_mono D hD h
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]; linarith

lemma rp_ro_cont (z : ℝ) (hz : z < D.b) : Continuous (fun p => ro D p z) := by
  obtain ⟨M, hM0, hM⟩ := rp_F_lip D hD
  have key : ∀ p q, ro D p z - ro D q z ≤ (D.b - z) * M * |p - q| := by
    intro p q
    obtain ⟨y, hzy, hyb, hy⟩ := rp_ro_attain D hD z p hz
    have h1 := rp_T_le_ro D hD q z y hzy
    have h2 := rp_Fbar_abs D hD M hM q p
    have h3 : (y - z) * (D.Fbar q - D.Fbar p) ≤ (D.b - z) * (M * |p - q|) := by
      calc (y - z) * (D.Fbar q - D.Fbar p) ≤ (y - z) * |D.Fbar q - D.Fbar p| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
        _ ≤ (D.b - z) * (M * |p - q|) := by
            rw [abs_sub_comm p q]
            exact mul_le_mul (by linarith) h2 (abs_nonneg _) (by linarith)
    have e : (y - z) * (D.Fbar y - D.Fbar p) =
        (y - z) * (D.Fbar y - D.Fbar q) + (y - z) * (D.Fbar q - D.Fbar p) := by ring
    rw [hy, e]
    have : (D.b - z) * M * |p - q| = (D.b - z) * (M * |p - q|) := by ring
    linarith
  apply LipschitzWith.continuous (K := Real.toNNReal ((D.b - z) * M))
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hK : 0 ≤ (D.b - z) * M := mul_nonneg (by linarith) hM0
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK, abs_sub_le_iff]
  constructor
  · exact key p q
  · have := key q p; rw [abs_sub_comm q p] at this; exact this

/-- `(1+β) π(p,z) - α (y-z)(F̄y - F̄p) = (1+β) π(p,w) - α (y-z) F̄(y)` with
`w = z - α/(1+β) (y - z)`. -/
lemma rp_H_eq (α β z y p : ℝ) (hβ : 0 ≤ β) :
    (1 + β) * revenue D p z - α * ((y - z) * (D.Fbar y - D.Fbar p)) =
      (1 + β) * revenue D p (z - α / (1 + β) * (y - z)) - α * (y - z) * D.Fbar y := by
  have hc : (1 + β) * (α / (1 + β)) = α := by field_simp
  unfold revenue
  linear_combination (-(y - z) * D.Fbar p) * hc

lemma rp_logFbar_tangent (hIFR : D.IFR) (p : ℝ) (hpa : D.a ≤ p) (hpb : p < D.b) :
    D.Fbar p ≤ Real.exp (-(D.f D.a) * (p - D.a)) := by
  have hFa : D.Fbar D.a = 1 := rp_Fbar_le_a D hD D.a le_rfl
  have hderiv : ∀ q ∈ Set.Ioo D.a D.b,
      HasDerivAt (fun x => Real.log (D.Fbar x) + D.f D.a * (x - D.a))
        (-D.f q / D.Fbar q + D.f D.a) q := fun q hq => by
    have h1 := (rp_Fbar_deriv D hD q hq).log (ne_of_gt (rp_Fbar_pos D hD hIFR q hq.2))
    have h2 := ((hasDerivAt_id' q).sub_const D.a).const_mul (D.f D.a)
    have h3 := h1.add h2
    rw [mul_one] at h3
    exact h3
  have hanti : AntitoneOn (fun x => Real.log (D.Fbar x) + D.f D.a * (x - D.a))
      (Set.Ico D.a D.b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico _ _)
    · exact (((rp_Fbar_cont D hD).continuousOn).log
        (fun x hx => ne_of_gt (rp_Fbar_pos D hD hIFR x hx.2))).add
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    · rw [interior_Ico]
      exact fun q hq => (hderiv q hq).differentiableAt.differentiableWithinAt
    · rw [interior_Ico]
      intro q hq
      rw [(hderiv q hq).deriv]
      have := hIFR (show D.a ∈ Set.Iio D.b from hD.2.1) (show q ∈ Set.Iio D.b from hq.2) hq.1.le
      unfold WTP.h at this
      rw [hFa, div_one] at this
      rw [neg_div]; linarith
  have := hanti ⟨le_rfl, hD.2.1⟩ ⟨hpa, hpb⟩ hpa
  simp only [hFa, Real.log_one, sub_self, mul_zero, add_zero] at this
  have hlog : Real.log (D.Fbar p) ≤ -(D.f D.a) * (p - D.a) := by linarith
  calc D.Fbar p = Real.exp (Real.log (D.Fbar p)) :=
        (Real.exp_log (rp_Fbar_pos D hD hIFR p hpb)).symm
    _ ≤ _ := Real.exp_le_exp.2 hlog

lemma rp_prop1a (hIFR : D.IFR) (α β : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1) (z : ℝ) (hz : 0 ≤ z ∧ z < D.b) :
    (∃! p, IsRegretPrice D α β z p) ∧
      (D.h D.a * (D.a - z) * (1 + α / (1 + β)) > 1 → IsRegretPrice D α β z D.a) := by
  obtain ⟨⟨pstar, hpstar, huniq⟩, -⟩ := rp_unbiased D hD hIFR z hz
  obtain ⟨hro, hru, hru0⟩ := rp_lemma1 D hD hIFR z ⟨hz.1, hz.2.le⟩ pstar hpstar
  obtain ⟨hlo, -⟩ := rp_eq15 D hD hIFR α β hα hβ z hz pstar hpstar
  set G := fun p => (1 + β) * revenue D p z - α * ro D p z with hG
  have hπG : ∀ p, p ≤ pstar → πhat D α β p z = G p - β * πstar D z := by
    intro p hp; rw [hlo p hp]
  have hbeyond : ∀ p, pstar < p → πhat D α β p z < πhat D α β pstar z := by
    intro p hp
    have hlt : revenue D p z < revenue D pstar z := by
      rcases lt_or_eq_of_le (hpstar p) with h | h
      · exact h
      · exfalso
        have h1 : IsUnbiasedPrice D z p := fun p' => h ▸ hpstar p'
        have := huniq p h1; linarith
    unfold πhat
    rw [hru0 p hp.le, hru0 pstar le_rfl]
    have h2 := hro hp.le
    simp only at h2
    nlinarith [mul_le_mul_of_nonneg_left h2 hα.1]
  -- location of p*
  have hmid := rp_rev_pos D hD hIFR z ((z + D.b) / 2) (by linarith) (by linarith)
  have hrevp : 0 < revenue D pstar z := lt_of_lt_of_le hmid (hpstar _)
  have hpz : z < pstar := by
    by_contra h; push Not at h
    unfold revenue at hrevp
    have := mul_nonpos_of_nonpos_of_nonneg (show pstar - z ≤ 0 by linarith)
      (rp_Fbar_bds D hD pstar).1
    linarith
  have hpb : pstar < D.b := by
    by_contra h; push Not at h
    rw [rp_rev_ge_b D hD z pstar h] at hrevp; exact lt_irrefl _ hrevp
  -- G(p*) > 0 and G ≤ 0 on (-∞, z]
  have hGpos : 0 < G pstar := by
    obtain ⟨y, hzy, hyb, hy⟩ := rp_ro_attain D hD z pstar hz.2
    have hro_lt : ro D pstar z < revenue D pstar z := by
      rw [hy]
      have hFp := rp_Fbar_pos D hD hIFR pstar hpb
      have h1 := hpstar y
      unfold revenue at h1 hrevp ⊢
      rcases eq_or_lt_of_le hzy with h | h
      · rw [← h]; simp; linarith
      · nlinarith [mul_pos (show 0 < y - z by linarith) hFp]
    have hro0 := rp_ro_nonneg D hD pstar z
    simp only [hG]
    nlinarith [mul_le_mul_of_nonneg_right hα.2 hro0, mul_nonneg hβ.1 hrevp.le]
  have hGneg : ∀ p, p ≤ z → G p ≤ 0 := by
    intro p hp
    simp only [hG]
    have h1 : revenue D p z ≤ 0 := by
      unfold revenue
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (rp_Fbar_bds D hD p).1
    nlinarith [mul_nonneg hα.1 (rp_ro_nonneg D hD p z), mul_nonneg hβ.1 (neg_nonneg.2 h1)]
  -- every maximizer lies in (z, p*]
  have hmaxloc : ∀ q, IsRegretPrice D α β z q → z < q ∧ q ≤ pstar := by
    intro q hq
    have hqp := rp_prop2 D hD hIFR α β hα hβ z hz q pstar hq hpstar
    refine ⟨?_, hqp⟩
    by_contra h; push Not at h
    have := hq pstar
    rw [hπG q hqp, hπG pstar le_rfl] at this
    linarith [hGneg q h]
  constructor
  · -- existence
    have hGc : Continuous G := by
      simp only [hG]
      exact (continuous_const.mul (by unfold revenue; exact
        (continuous_id.sub continuous_const).mul (rp_Fbar_cont D hD))).sub
        (continuous_const.mul (rp_ro_cont D hD z hz.2))
    obtain ⟨p0, hp0, hmax⟩ := (isCompact_Icc (a := z) (b := pstar)).exists_isMaxOn
      (Set.nonempty_Icc.2 hpz.le) hGc.continuousOn
    have hGp0 : G pstar ≤ G p0 := hmax ⟨hpz.le, le_rfl⟩
    have hp0reg : IsRegretPrice D α β z p0 := by
      intro p'
      rw [hπG p0 hp0.2]
      by_cases h1 : pstar < p'
      · have := hbeyond p' h1
        rw [hπG pstar le_rfl] at this; linarith
      push Not at h1
      rw [hπG p' h1]
      by_cases h2 : z ≤ p'
      · have : G p' ≤ G p0 := hmax ⟨h2, h1⟩
        linarith
      · push Not at h2; have := hGneg p' h2.le; linarith
    refine ⟨p0, hp0reg, ?_⟩
    -- uniqueness
    have key : ∀ q1 q2, IsRegretPrice D α β z q1 → IsRegretPrice D α β z q2 → ¬ q1 < q2 := by
      intro q1 q2 h1 h2 hlt
      obtain ⟨hz1, hp1⟩ := hmaxloc q1 h1
      obtain ⟨hz2, hp2⟩ := hmaxloc q2 h2
      set m := (q1 + q2) / 2 with hm
      have hmp : m ≤ pstar := by linarith
      have hGq1m : G m ≤ G q1 := by
        have := h1 m; rw [hπG m hmp, hπG q1 hp1] at this; linarith
      have hGq2m : G m ≤ G q2 := by
        have := h2 m; rw [hπG m hmp, hπG q2 hp2] at this; linarith
      obtain ⟨y, hzy, hyb, hy⟩ := rp_ro_attain D hD z m hz.2
      set w := z - α / (1 + β) * (y - z) with hw
      have hwz : w ≤ z := by
        have : 0 ≤ α / (1 + β) * (y - z) :=
          mul_nonneg (div_nonneg hα.1 (by linarith)) (by linarith)
        linarith
      have hGm : G m = (1 + β) * revenue D m w - α * (y - z) * D.Fbar y := by
        simp only [hG]; rw [hy, rp_H_eq D hD α β z y m hβ.1]
      have hGq : ∀ q, G q ≤ (1 + β) * revenue D q w - α * (y - z) * D.Fbar y := by
        intro q
        simp only [hG]
        rw [← rp_H_eq D hD α β z y q hβ.1]
        have := rp_T_le_ro D hD q z y hzy
        nlinarith [mul_le_mul_of_nonneg_left this hα.1]
      have hs := rp_rev_sqc D hD hIFR w q1 m q2 (by linarith) (by linarith) (by linarith)
        (by linarith)
      rcases min_lt_iff.1 hs with h | h
      · have := hGq q1
        nlinarith [mul_lt_mul_of_pos_left h (show (0:ℝ) < 1 + β by linarith)]
      · have := hGq q2
        nlinarith [mul_lt_mul_of_pos_left h (show (0:ℝ) < 1 + β by linarith)]
    intro q hq
    rcases lt_trichotomy q p0 with h | h | h
    · exact absurd h (key q p0 hq hp0reg)
    · exact h
    · exact absurd h (key p0 q hp0reg hq)
  · -- the corner case
    intro hcorner
    have hFa : D.Fbar D.a = 1 := rp_Fbar_le_a D hD D.a le_rfl
    have hha : D.h D.a = D.f D.a := by unfold WTP.h; rw [hFa, div_one]
    obtain ⟨c, hc⟩ : ∃ c, c = α / (1 + β) := ⟨_, rfl⟩
    have h1b : (0:ℝ) < 1 + β := by linarith
    have hc' : (1 + β) * c = α := by rw [hc]; field_simp [h1b.ne']
    rw [hha, ← hc] at hcorner
    have hc0 : 0 ≤ c := by rw [hc]; exact div_nonneg hα.1 h1b.le
    have hfa0 : 0 ≤ D.f D.a := hD.2.2.1 D.a
    have haz : z < D.a := by
      by_contra h; push Not at h
      have : D.f D.a * (D.a - z) * (1 + c) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos hfa0 (by linarith)) (by linarith)
      linarith
    obtain ⟨w, hw⟩ : ∃ w, w = z - c * (D.a - z) := ⟨_, rfl⟩
    have haw : D.a - w = (D.a - z) * (1 + c) := by rw [hw]; ring
    have hk : 1 < D.f D.a * (D.a - w) := by rw [haw]; linarith
    have hawpos : 0 < D.a - w := by rw [haw]; positivity
    -- π(·, w) ≤ a - w
    have hrevw : ∀ p, revenue D p w ≤ D.a - w := by
      intro p
      unfold revenue
      by_cases hpa : p ≤ D.a
      · rw [rp_Fbar_le_a D hD p hpa]; linarith
      push Not at hpa
      by_cases hpb' : D.b ≤ p
      · rw [WTP.Fbar, rp_F_eq_one D hD p hpb']; simp; linarith
      push Not at hpb'
      have ht := rp_logFbar_tangent D hD hIFR p hpa.le hpb'
      set t := p - D.a with htdef
      have htpos : 0 < t := by linarith
      have hexp : 1 + D.f D.a * t ≤ Real.exp (D.f D.a * t) := by
        have := Real.add_one_le_exp (D.f D.a * t); linarith
      have hpw : p - w ≤ (D.a - w) * Real.exp (D.f D.a * t) := by
        have : p - w = (D.a - w) + t := by rw [htdef]; ring
        rw [this]
        have h2 : t ≤ (D.a - w) * (D.f D.a * t) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hexp hawpos.le]
      have hFb : 0 ≤ D.Fbar p := (rp_Fbar_bds D hD p).1
      have e : Real.exp (-(D.f D.a) * t) * Real.exp (D.f D.a * t) = 1 := by
        rw [← Real.exp_add]; simp
      calc (p - w) * D.Fbar p ≤ ((D.a - w) * Real.exp (D.f D.a * t)) * Real.exp (-(D.f D.a) * t) :=
            mul_le_mul hpw ht hFb (by positivity)
        _ = D.a - w := by rw [mul_assoc, mul_comm (Real.exp _) (Real.exp _), e, mul_one]
    -- G ≤ G(a)
    have hro_a : ro D D.a z = 0 := by
      apply le_antisymm _ (rp_ro_nonneg D hD D.a z)
      unfold ro
      haveI : Nonempty {y : ℝ // y < D.a} := ⟨⟨D.a - 1, by linarith⟩⟩
      apply ciSup_le
      intro y
      rw [rp_Fbar_le_a D hD y.1 y.2.le, hFa]; simp
    have hGa : G D.a = (1 + β) * (D.a - z) := by
      simp only [hG]; rw [hro_a]; unfold revenue; rw [hFa]; ring
    have hGle : ∀ p, G p ≤ G D.a := by
      intro p
      have h1 := rp_T_le_ro D hD p z D.a haz.le
      have h2 := rp_H_eq D hD α β z D.a p hβ.1
      rw [← hc, ← hw, hFa] at h2
      have h3 := hrevw p
      rw [hGa]
      simp only [hG]
      have h4 : (1 + β) * (D.a - w) - α * (D.a - z) = (1 + β) * (D.a - z) := by
        rw [haw]; linear_combination (D.a - z) * hc'
      rw [hFa] at h1
      have e1 : α * ((D.a - z) * (1 - D.Fbar p)) ≤ α * ro D p z :=
        mul_le_mul_of_nonneg_left h1 hα.1
      have e2 : (1 + β) * revenue D p w ≤ (1 + β) * (D.a - w) :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
      linarith
    have hap : D.a ≤ pstar := by
      by_contra h; push Not at h
      have := hpstar D.a
      unfold revenue at this
      rw [hFa, rp_Fbar_le_a D hD pstar h.le] at this
      linarith
    intro p'
    rw [hπG D.a hap]
    by_cases h1 : pstar < p'
    · have := hbeyond p' h1
      rw [hπG pstar le_rfl] at this
      linarith [hGle pstar]
    push Not at h1
    rw [hπG p' h1]
    linarith [hGle p']

end RPProp1

section RPEq14

variable (D : WTP) (hD : D.Standing)
include hD

lemma rp_πstar_anti : AntitoneOn (πstar D) (Set.Icc 0 D.b) := by
  intro z hz z' hz' hzz
  unfold πstar
  apply ciSup_le
  intro p
  have : revenue D p z' ≤ revenue D p z := by
    unfold revenue; nlinarith [(rp_Fbar_bds D hD p).1]
  exact le_trans this (le_ciSup (f := fun q => revenue D q z)
    ⟨D.b - z, by rintro _ ⟨q, rfl⟩; exact rp_rev_le D hD z hz.2 q⟩ p)

lemma rp_eq14_deriv (hIFR : D.IFR) (z : ℝ) (hz : z < D.b) (p : ℝ)
    (hp : IsUnbiasedPrice D z p) : HasDerivAt (πstar D) (-(D.Fbar p)) z := by
  obtain ⟨M, hM0, hM⟩ := rp_F_lip D hD
  obtain ⟨⟨p0, hp0, huniq⟩, hunim⟩ := rp_unbiased_gen D hD hIFR z ⟨trivial, hz⟩
  obtain ⟨hmo, han⟩ := hunim p hp
  have hex : ∀ z', z' < D.b → ∃ p', IsUnbiasedPrice D z' p' := fun z' h' =>
    ((rp_unbiased_gen D hD hIFR z' ⟨trivial, h'⟩).1).exists
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨η, hη⟩ : ∃ η, η = c / (M + 1) := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; positivity
  have hMη : M * η ≤ c := by
    rw [hη, mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  have gp : revenue D (p + η) z < revenue D p z := by
    rcases lt_or_eq_of_le (hp (p + η)) with h | h
    · exact h
    · exfalso
      have : IsUnbiasedPrice D z (p + η) := fun q => h ▸ hp q
      have := (huniq _ this).trans (huniq p hp).symm; linarith
  have gm : revenue D (p - η) z < revenue D p z := by
    rcases lt_or_eq_of_le (hp (p - η)) with h | h
    · exact h
    · exfalso
      have : IsUnbiasedPrice D z (p - η) := fun q => h ▸ hp q
      have := (huniq _ this).trans (huniq p hp).symm; linarith
  obtain ⟨g, hg⟩ : ∃ g, g = min (revenue D p z - revenue D (p + η) z)
      (revenue D p z - revenue D (p - η) z) := ⟨_, rfl⟩
  have hgpos : 0 < g := by rw [hg]; exact lt_min (by linarith) (by linarith)
  have hg1 : g ≤ revenue D p z - revenue D (p + η) z := by rw [hg]; exact min_le_left _ _
  have hg2 : g ≤ revenue D p z - revenue D (p - η) z := by rw [hg]; exact min_le_right _ _
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = min (g / 2) (D.b - z) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; exact lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ g / 2 := by rw [hδ]; exact min_le_left _ _
  have hδ2 : δ ≤ D.b - z := by rw [hδ]; exact min_le_right _ _
  filter_upwards [Metric.ball_mem_nhds z hδpos] with z' hz'
  rw [Metric.mem_ball, Real.dist_eq] at hz'
  have hz'b : z' < D.b := by have := (abs_lt.1 hz').2; linarith
  obtain ⟨p', hp'⟩ := hex z' hz'b
  have shift : ∀ q, |revenue D q z' - revenue D q z| ≤ |z' - z| := by
    intro q; unfold revenue
    have h1 := rp_Fbar_bds D hD q
    rw [show (q - z') * D.Fbar q - (q - z) * D.Fbar q = -(z' - z) * D.Fbar q by ring, abs_mul,
      abs_neg, abs_of_nonneg h1.1]
    nlinarith [abs_nonneg (z' - z)]
  have hclose : |p' - p| ≤ η := by
    have s2 := abs_le.1 (shift p)
    have s1 := abs_le.1 (shift p')
    have h2 := hp' p
    rw [abs_le]; constructor
    · by_contra h; push Not at h
      have h1 : revenue D p' z ≤ revenue D (p - η) z :=
        hmo (show p' ∈ Set.Iic p by simp; linarith) (show p - η ∈ Set.Iic p by simp; linarith)
          (by linarith)
      linarith
    · by_contra h; push Not at h
      have h1 : revenue D p' z ≤ revenue D (p + η) z :=
        han (show p + η ∈ Set.Ici p by simp; linarith) (show p' ∈ Set.Ici p by simp; linarith)
          (by linarith)
      linarith
  have hπz : πstar D z = revenue D p z := rp_πstar_eq D hD z p hp
  have hπz' : πstar D z' = revenue D p' z' := rp_πstar_eq D hD z' p' hp'
  have lower : revenue D p z' ≤ revenue D p' z' := hp' p
  have upper : revenue D p' z ≤ revenue D p z := hp p'
  have hF : |D.Fbar p - D.Fbar p'| ≤ M * |p - p'| := rp_Fbar_abs D hD M hM p p'
  rw [hπz, hπz', Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul]
  unfold revenue at lower upper ⊢
  have hE0 : 0 ≤ (p' - z') * D.Fbar p' - (p - z) * D.Fbar p - (z' - z) * -D.Fbar p := by
    nlinarith
  have hE1 : (p' - z') * D.Fbar p' - (p - z) * D.Fbar p - (z' - z) * -D.Fbar p ≤
      (z' - z) * (D.Fbar p - D.Fbar p') := by nlinarith
  rw [abs_of_nonneg hE0]
  have h3 : (z' - z) * (D.Fbar p - D.Fbar p') ≤ |z' - z| * |D.Fbar p - D.Fbar p'| := by
    rw [← abs_mul]; exact le_abs_self _
  have h4 : |D.Fbar p - D.Fbar p'| ≤ c := by
    rw [abs_sub_comm p p'] at hF
    calc |D.Fbar p - D.Fbar p'| ≤ M * |p' - p| := hF
      _ ≤ M * η := mul_le_mul_of_nonneg_left hclose hM0
      _ ≤ c := hMη
  have h5 : |z' - z| * |D.Fbar p - D.Fbar p'| ≤ |z' - z| * c :=
    mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
  linarith

end RPEq14

theorem solution (D : WTP) (hD : D.Standing) (hIFR : D.IFR) :
    (∀ z ∈ Set.Ico 0 D.b, ∀ p, IsUnbiasedPrice D z p → HasDerivAt (πstar D) (-(D.Fbar p)) z) ∧
      AntitoneOn (πstar D) (Set.Icc 0 D.b) :=
  ⟨fun z hz p hp => rp_eq14_deriv D hD hIFR z hz.2 p hp, rp_πstar_anti D hD⟩
