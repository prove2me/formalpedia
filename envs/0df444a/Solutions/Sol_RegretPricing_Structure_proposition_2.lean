-- Prove2me | solution 1 for RegretPricing.Structure.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T16:20:19.38904+00:00
-- url     : https://prove2.me/submissions/8c2d056d-388a-4dd1-9073-6f37b1831873

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


lemma rp_unbiased (hIFR : D.IFR) (z : ℝ)
    (hz : 0 ≤ z ∧ z < D.b) :
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

theorem solution (D : WTP) (hD : D.Standing) (hIFR : D.IFR) (α β : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1) (z : ℝ) (hz : 0 ≤ z ∧ z < D.b)
    (phat pstar : ℝ) (hphat : IsRegretPrice D α β z phat) (hpstar : IsUnbiasedPrice D z pstar) :
    phat ≤ pstar :=
  rp_prop2 D hD hIFR α β hα hβ z hz phat pstar hphat hpstar
