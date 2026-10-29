-- Prove2me | solution 1 for ZipkinLostSales.Bounds.corollary_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T03:06:52.997101+00:00
-- url     : https://prove2.me/submissions/01753081-7e8f-4687-a02f-5af3130eedc4

import Mathlib
import Definitions.Def_ZipkinLostSales_Bounds_Model
import Theorems.Thm_ZipkinLostSales_LNatural_theorem_4
set_option autoImplicit false
open ZipkinLostSales.Bounds MeasureTheory
open ZipkinLostSales.LNatural (vext)

theorem c47_onHand_z {L : ℕ} (v : Fin L → ℝ) (z : ℝ) (D : Fin L → ℝ) :
    ∀ j, j < L → onHand v z D j = onHand v 0 D j := by
  intro j
  induction j with
  | zero => intro h; simp [onHand, arrival, h]
  | succ j ih => intro h; simp [onHand, arrival, h, ih (by omega)]

theorem c47_yPlusL_z {L : ℕ} (hL : 0 < L) (v : Fin L → ℝ) (z : ℝ) (D : Fin L → ℝ) :
    yPlusL v z D = yPlusL v 0 D + z := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  simp only [yPlusL, onHand, arrival, lt_self_iff_false, if_false]
  rw [c47_onHand_z v z D m (by omega)]; ring

theorem c47_yPlusL_nonneg {L : ℕ} (hL : 0 < L) (v : Fin L → ℝ) (D : Fin L → ℝ) :
    0 ≤ yPlusL v 0 D := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  simp only [yPlusL, onHand, arrival, lt_self_iff_false, if_false, add_zero]
  exact le_max_right _ _

theorem c47_onHand_ge {L : ℕ} (v : Fin L → ℝ) (D : Fin L → ℝ) (l : ℕ) :
    ∀ j, l ≤ j → j < L →
      vext v l - vext v (j + 1) - ∑ i ∈ Finset.Ico l j, vext D i ≤ onHand v 0 D j := by
  intro j
  induction j with
  | zero =>
    intro hl hL
    have : l = 0 := by omega
    subst this
    simp [onHand, arrival, hL, xext]
  | succ j ih =>
    intro hl hL
    rcases Nat.eq_or_lt_of_le hl with h | h
    · subst h
      simp only [Finset.Ico_self, Finset.sum_empty, sub_zero]
      simp only [onHand, arrival, if_pos hL, xext]
      have := le_max_right (onHand v 0 D j - vext D j) 0
      linarith
    · have ih' := ih (by omega) (by omega)
      rw [Finset.sum_Ico_succ_top (by omega)]
      simp only [onHand, arrival, if_pos hL, xext]
      have := le_max_left (onHand v 0 D j - vext D j) 0
      linarith

theorem c47_yPlusL_ge {L : ℕ} (v : Fin L → ℝ) (D : Fin L → ℝ) (l : ℕ) (hl : l < L) :
    vext v l - ∑ i ∈ Finset.Ico l L, vext D i ≤ yPlusL v 0 D := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  have h1 := c47_onHand_ge v D l m (by omega) (by omega)
  rw [Finset.sum_Ico_succ_top (by omega)]
  have hv : vext v (m + 1) = 0 := by simp [vext]
  simp only [yPlusL, onHand, arrival, lt_self_iff_false, if_false, add_zero]
  have := le_max_left (onHand v 0 D m - vext D m) 0
  rw [hv] at h1; linarith

/-- One-variable increment bound for `q0`. -/
theorem c47_q0_diff (M : Data) [IsProbabilityMeasure M.μ] (hint : Integrable id M.μ)
    (hph : 0 < M.p + M.h) {y₁ y₂ : ℝ} (h12 : y₁ ≤ y₂) :
    (y₂ - y₁) * ((M.c + M.h) - (M.p + M.h) * (M.μ (Set.Ioi y₁)).toReal)
      ≤ q0 M y₂ - q0 M y₁ := by
  have hA : ∀ y : ℝ, Integrable (fun d => max (y - d) 0) M.μ := fun y =>
    ((integrable_const y).sub hint).pos_part
  have hB : ∀ y : ℝ, ∫ d, max (d - y) 0 ∂M.μ = ∫ d, max (y - d) 0 ∂M.μ - y + ∫ d, d ∂M.μ := by
    intro y
    have : (fun d => max (d - y) 0) = fun d => (max (y - d) 0 - y) + id d := by
      funext d; simp only [id]
      rcases le_total d y with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    have h1 : Integrable (fun d => max (y - d) 0 - y) M.μ := (hA y).sub (integrable_const y)
    rw [this, integral_add h1 hint, integral_sub (hA y) (integrable_const y)]
    simp [id]
  have hkey : (y₂ - y₁) * (M.μ (Set.Iic y₁)).toReal ≤
      ∫ d, max (y₂ - d) 0 ∂M.μ - ∫ d, max (y₁ - d) 0 ∂M.μ := by
    rw [← integral_sub (hA y₂) (hA y₁)]
    have hind : ∫ d, (Set.Iic y₁).indicator (fun _ => y₂ - y₁) d ∂M.μ
        = (y₂ - y₁) * (M.μ (Set.Iic y₁)).toReal := by
      rw [integral_indicator_const _ measurableSet_Iic]
      simp [Measure.real, smul_eq_mul, mul_comm]
    rw [← hind]
    apply integral_mono ((integrable_const _).indicator measurableSet_Iic)
      ((hA y₂).sub (hA y₁))
    intro d
    simp only [Pi.sub_apply]
    by_cases hd : d ≤ y₁
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hd)]
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · rw [Set.indicator_of_notMem (by simpa using hd)]
      have := max_le_max_right 0 (show y₁ - d ≤ y₂ - d by linarith)
      linarith
  have hsplit : (M.μ (Set.Iic y₁)).toReal + (M.μ (Set.Ioi y₁)).toReal = 1 := by
    rw [← Set.compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
    simp
  unfold q0
  rw [hB y₂, hB y₁]
  have h2 := mul_le_mul_of_nonneg_left hkey hph.le
  have hI : (M.μ (Set.Iic y₁)).toReal = 1 - (M.μ (Set.Ioi y₁)).toReal := by linarith
  rw [hI] at h2
  ring_nf; ring_nf at h2; linarith

theorem c47_theta_pos {L : ℕ} (M : Data) (hM : Assumptions L M) : 0 < θbar M ∧ θbar M < 1 := by
  have hph : 0 < M.p + M.h := lt_trans hM.hch hM.hph
  refine ⟨div_pos hM.hch hph, ?_⟩
  unfold θbar; rw [div_lt_one hph]; exact hM.hph

theorem c47_tail_le {L : ℕ} (M : Data) (hM : Assumptions L M) (l : Fin (L + 1)) (s : ℝ)
    (hs : sbar L M l ≤ s) :
    ((Measure.pi fun _ : Fin (L + 1) => M.μ) {D | s < ∑ j ∈ Finset.Ici l, D j}).toReal
      ≤ θbar M := by
  haveI := hM.prob
  set P := Measure.pi fun _ : Fin (L + 1) => M.μ with hP
  set X : (Fin (L + 1) → ℝ) → ℝ := fun D => ∑ j ∈ Finset.Ici l, D j with hX
  have hXm : Measurable X := Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)
  have hmeas : ∀ t : ℝ, MeasurableSet {D | t < X D} := fun t =>
    measurableSet_lt measurable_const hXm
  obtain ⟨hθ0, -⟩ := c47_theta_pos M hM
  set S := {s : ℝ | (P {D | s < X D}).toReal ≤ θbar M} with hS
  have hne : S.Nonempty := by
    have hanti : Antitone (fun n : ℕ => {D | (n : ℝ) < X D}) := by
      intro a b hab D hD
      simp only [Set.mem_setOf_eq] at *
      exact lt_of_le_of_lt (by exact_mod_cast hab) hD
    have hlim := tendsto_measure_iInter_atTop (μ := P) (s := fun n : ℕ => {D | (n : ℝ) < X D})
      (fun n : ℕ => (hmeas (n : ℝ)).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ n : ℕ, {D | (n : ℝ) < X D}) = ∅ := by
      ext D
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_forall, not_lt]
      exact exists_nat_ge (X D)
    rw [hempty, measure_empty] at hlim
    have hpos : (0 : ENNReal) < ENNReal.ofReal (θbar M) := ENNReal.ofReal_pos.mpr hθ0
    obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).2 _ hpos).exists
    refine ⟨n, ?_⟩
    show (P {D | (n : ℝ) < X D}).toReal ≤ θbar M
    exact ENNReal.toReal_le_of_le_ofReal hθ0.le hn.le
  have hgt : ∀ t, sbar L M l < t → (P {D | t < X D}).toReal ≤ θbar M := by
    intro t ht
    have ht' : sInf S < t := ht
    obtain ⟨a, ha, hat⟩ := exists_lt_of_csInf_lt hne ht'
    refine le_trans ?_ ha
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun D hD => lt_trans hat hD))
  have hmono : Monotone (fun n : ℕ => {D | s + 1 / ((n : ℝ) + 1) < X D}) := by
    intro a b hab D hD
    simp only [Set.mem_setOf_eq] at *
    have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
    linarith
  have hU : (⋃ n : ℕ, {D | s + 1 / ((n : ℝ) + 1) < X D}) = {D | s < X D} := by
    ext D
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨n, by linarith⟩
  have hlim := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hU] at hlim
  have hle : P {D | s < X D} ≤ ENNReal.ofReal (θbar M) := by
    refine le_of_tendsto' hlim (fun n => ?_)
    simp only [Function.comp_apply]
    have h1 := hgt (s + 1 / ((n : ℝ) + 1))
      (by have : 0 < 1 / ((n : ℝ) + 1) := by positivity
          linarith)
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hθ0.le).mpr h1
  exact ENNReal.toReal_le_of_le_ofReal hθ0.le hle

theorem c47_sum_split {L : ℕ} (l : ℕ) (hl : l < L + 1) (D' : Fin (L + 1) → ℝ) :
    ∑ j ∈ Finset.Ici (⟨l, hl⟩ : Fin (L + 1)), D' j
      = D' (Fin.last L) + ∑ i ∈ Finset.Ico l L, vext (fun j : Fin L => D' j.castSucc) i := by
  have h1 : Finset.Ici (⟨l, hl⟩ : Fin (L + 1))
      = Finset.univ.filter (fun j => (⟨l, hl⟩ : Fin (L + 1)) ≤ j) := by
    ext j; simp
  have h2 : Finset.Ico l L = (Finset.range L).filter (fun i => l ≤ i) := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]; omega
  rw [h1, Finset.sum_filter, h2, Finset.sum_filter, Fin.sum_univ_castSucc,
    ← Fin.sum_univ_eq_sum_range (fun i => if l ≤ i then vext (fun j : Fin L => D' j.castSucc) i
      else 0) L]
  have hlast : (⟨l, hl⟩ : Fin (L + 1)) ≤ Fin.last L := Fin.le_last _
  rw [if_pos hlast, add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [vext, Fin.le_iff_val_le_val]

theorem c47_vext_meas {L : ℕ} (j : ℕ) : Measurable (fun D : Fin L → ℝ => vext D j) := by
  by_cases h : j < L
  · simp only [vext, h, dif_pos]; exact measurable_pi_apply _
  · simp only [vext, h, dif_neg, not_false_eq_true]; exact measurable_const

theorem c47_prod_tail {L : ℕ} (M : Data) [IsProbabilityMeasure M.μ] (l : ℕ) (hl : l < L + 1)
    (s : ℝ) :
    ∫ D, (M.μ (Set.Ioi (s - ∑ i ∈ Finset.Ico l L, vext D i))).toReal
        ∂(Measure.pi fun _ : Fin L => M.μ)
      = ((Measure.pi fun _ : Fin (L + 1) => M.μ)
          {D' | s < ∑ j ∈ Finset.Ici (⟨l, hl⟩ : Fin (L + 1)), D' j}).toReal := by
  have hS : Measurable (fun D : Fin L → ℝ => ∑ i ∈ Finset.Ico l L, vext D i) :=
    Finset.measurable_sum _ (fun i _ => c47_vext_meas i)
  set B : Set (ℝ × (Fin L → ℝ)) := {p | s < p.1 + ∑ i ∈ Finset.Ico l L, vext p.2 i} with hBdef
  have hB : MeasurableSet B :=
    measurableSet_lt measurable_const (measurable_fst.add (hS.comp measurable_snd))
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (L + 1) => M.μ) (Fin.last L)
  have hpre : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (L + 1) => ℝ) (Fin.last L)) ⁻¹' B
      = {D' | s < ∑ j ∈ Finset.Ici (⟨l, hl⟩ : Fin (L + 1)), D' j} := by
    ext D'
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hBdef, c47_sum_split l hl D']
    simp [MeasurableEquiv.piFinSuccAbove_apply]
    rfl
  have hanti : Antitone (fun t : ℝ => M.μ (Set.Ioi t)) := fun a b hab =>
    measure_mono (Set.Ioi_subset_Ioi hab)
  rw [← hpre, hmp.measure_preimage hB.nullMeasurableSet, Measure.prod_apply_symm hB]
  rw [integral_toReal]
  · congr 1
    refine lintegral_congr (fun D => ?_)
    congr 1
    ext d
    simp only [Set.mem_Ioi, Set.mem_preimage, hBdef, Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  · exact (hanti.measurable.comp (measurable_const.sub hS)).aemeasurable
  · exact Filter.Eventually.of_forall (fun _ => measure_lt_top _ _)

theorem c47_onHand_meas {L : ℕ} (v : Fin L → ℝ) (z : ℝ) :
    ∀ j, Measurable (fun D : Fin L → ℝ => onHand v z D j) := by
  intro j
  induction j with
  | zero => simp only [onHand]; exact measurable_const
  | succ j ih =>
    simp only [onHand]
    exact ((ih.sub (c47_vext_meas j)).max measurable_const).add measurable_const

theorem c47_q0_repr (M : Data) [IsProbabilityMeasure M.μ] (hint : Integrable id M.μ) (y : ℝ) :
    q0 M y = (M.c - M.p) * y + M.p * ∫ d, d ∂M.μ + (M.h + M.p) * ∫ d, max (y - d) 0 ∂M.μ := by
  have hA : Integrable (fun d => max (y - d) 0) M.μ := ((integrable_const y).sub hint).pos_part
  have hB : ∫ d, max (d - y) 0 ∂M.μ = ∫ d, max (y - d) 0 ∂M.μ - y + ∫ d, d ∂M.μ := by
    have : (fun d => max (d - y) 0) = fun d => (max (y - d) 0 - y) + id d := by
      funext d; simp only [id]
      rcases le_total d y with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    have h1 : Integrable (fun d => max (y - d) 0 - y) M.μ := hA.sub (integrable_const y)
    rw [this, integral_add h1 hint, integral_sub hA (integrable_const y)]
    simp [id]
  unfold q0; rw [hB]; ring

theorem c47_A_lip (M : Data) [IsProbabilityMeasure M.μ] (hint : Integrable id M.μ) (a b : ℝ) :
    |∫ d, max (a - d) 0 ∂M.μ - ∫ d, max (b - d) 0 ∂M.μ| ≤ |a - b| := by
  have hA : ∀ y : ℝ, Integrable (fun d => max (y - d) 0) M.μ := fun y =>
    ((integrable_const y).sub hint).pos_part
  rw [← integral_sub (hA a) (hA b)]
  have h := norm_integral_le_of_norm_le_const (μ := M.μ) (C := |a - b|)
    (f := fun d => max (a - d) 0 - max (b - d) 0)
    (Filter.Eventually.of_forall (fun d => by
      rw [Real.norm_eq_abs]
      have := abs_max_sub_max_le_abs (a - d) (b - d) 0
      rwa [show a - d - (b - d) = a - b by ring] at this))
  simpa [Real.norm_eq_abs] using h

theorem c47_q0_lip (M : Data) [IsProbabilityMeasure M.μ] (hint : Integrable id M.μ) (a b : ℝ) :
    |q0 M a - q0 M b| ≤ (|M.c - M.p| + |M.h + M.p|) * |a - b| := by
  rw [c47_q0_repr M hint a, c47_q0_repr M hint b]
  have h1 := c47_A_lip M hint a b
  have : (M.c - M.p) * a + M.p * ∫ d, d ∂M.μ + (M.h + M.p) * ∫ d, max (a - d) 0 ∂M.μ -
      ((M.c - M.p) * b + M.p * ∫ d, d ∂M.μ + (M.h + M.p) * ∫ d, max (b - d) 0 ∂M.μ)
      = (M.c - M.p) * (a - b) + (M.h + M.p) * (∫ d, max (a - d) 0 ∂M.μ
          - ∫ d, max (b - d) 0 ∂M.μ) := by ring
  rw [this]
  calc _ ≤ |(M.c - M.p) * (a - b)| + |(M.h + M.p) * (∫ d, max (a - d) 0 ∂M.μ
          - ∫ d, max (b - d) 0 ∂M.μ)| := abs_add_le _ _
    _ ≤ |M.c - M.p| * |a - b| + |M.h + M.p| * |a - b| := by
        rw [abs_mul, abs_mul]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
    _ = _ := by ring

theorem c47_q0_cont (M : Data) [IsProbabilityMeasure M.μ] (hint : Integrable id M.μ) :
    Continuous (q0 M) := by
  have : LipschitzWith ⟨|M.c - M.p| + |M.h + M.p|, by positivity⟩ (q0 M) :=
    LipschitzWith.of_dist_le_mul (fun a b => by
      rw [Real.dist_eq, Real.dist_eq]; exact c47_q0_lip M hint a b)
  exact this.continuous

theorem c47_int_tail {L : ℕ} (M : Data) [IsProbabilityMeasure M.μ]
    (φ : (Fin L → ℝ) → ℝ) (hφ : Measurable φ) :
    Integrable (fun D => (M.μ (Set.Ioi (φ D))).toReal) (Measure.pi fun _ : Fin L => M.μ) := by
  have hanti : Antitone (fun t : ℝ => (M.μ (Set.Ioi t)).toReal) := fun a b hab =>
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ioi_subset_Ioi hab))
  refine (integrable_const (1 : ℝ)).mono' (hanti.measurable.comp hφ).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun D => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

theorem c47_intT_le {L : ℕ} (M : Data) (hM : Assumptions L M) (v : Fin L → ℝ) (z₁ : ℝ)
    (hb : sbar L M (Fin.last L) ≤ z₁ ∨ ∃ l : Fin L, sbar L M l.castSucc ≤ v l + z₁) :
    ∫ D, (M.μ (Set.Ioi (yPlusL v 0 D + z₁))).toReal ∂(Measure.pi fun _ : Fin L => M.μ)
      ≤ θbar M := by
  haveI := hM.prob
  have hanti : Antitone (fun t : ℝ => (M.μ (Set.Ioi t)).toReal) := fun a b hab =>
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ioi_subset_Ioi hab))
  have hYm : Measurable (fun D : Fin L → ℝ => yPlusL v 0 D) := c47_onHand_meas v 0 L
  have hS : ∀ l, Measurable (fun D : Fin L → ℝ => ∑ i ∈ Finset.Ico l L, vext D i) := fun l =>
    Finset.measurable_sum _ (fun i _ => c47_vext_meas i)
  rcases hb with hb | ⟨l, hl⟩
  · calc _ ≤ ∫ D, (M.μ (Set.Ioi (z₁ - ∑ i ∈ Finset.Ico L L, vext D i))).toReal
            ∂(Measure.pi fun _ : Fin L => M.μ) := by
          refine integral_mono (c47_int_tail M _ (hYm.add measurable_const))
            (c47_int_tail M _ (measurable_const.sub (hS L))) (fun D => ?_)
          apply hanti
          simp only [Finset.Ico_self, Finset.sum_empty, sub_zero]
          have := c47_yPlusL_nonneg hM.hL v D
          linarith
      _ = _ := c47_prod_tail M L (Nat.lt_succ_self L) z₁
      _ ≤ θbar M := c47_tail_le M hM _ z₁ hb
  · calc _ ≤ ∫ D, (M.μ (Set.Ioi ((v l + z₁) - ∑ i ∈ Finset.Ico (l : ℕ) L, vext D i))).toReal
            ∂(Measure.pi fun _ : Fin L => M.μ) := by
          refine integral_mono (c47_int_tail M _ (hYm.add measurable_const))
            (c47_int_tail M _ (measurable_const.sub (hS l))) (fun D => ?_)
          apply hanti
          have := c47_yPlusL_ge v D l l.isLt
          have hv : vext v l = v l := by simp [vext]
          rw [hv] at this
          linarith
      _ = _ := c47_prod_tail M l (by omega) (v l + z₁)
      _ ≤ θbar M := c47_tail_le M hM _ (v l + z₁) hl

/-- Child B: `q` is nondecreasing beyond the Karlin–Scarf–Morton bound. -/
theorem childB_q_mono_beyond {L : ℕ} (M : Data) (hM : Assumptions L M) (v : Fin L → ℝ)
    (hv : v ∈ ZipkinLostSales.LNatural.V L) (z₁ z₂ : ℝ) (h0 : 0 ≤ z₁) (h12 : z₁ ≤ z₂)
    (hb : sbar L M (Fin.last L) ≤ z₁ ∨ ∃ l : Fin L, sbar L M l.castSucc ≤ v l + z₁) :
    q M v z₁ ≤ q M v z₂ := by
  haveI := hM.prob
  set ν := Measure.pi fun _ : Fin L => M.μ with hν
  have hph : 0 < M.p + M.h := lt_trans hM.hch hM.hph
  have hcont : Continuous (q0 M) := c47_q0_cont M hM.integrable
  have hYm : Measurable (fun D : Fin L → ℝ => yPlusL v 0 D) := c47_onHand_meas v 0 L
  have hf : ∀ z, (fun D => q0 M (yPlusL v z D)) = fun D => q0 M (yPlusL v 0 D + z) :=
    fun z => funext (fun D => by rw [c47_yPlusL_z hM.hL])
  have hfm : ∀ z, AEStronglyMeasurable (fun D => q0 M (yPlusL v 0 D + z)) ν := fun z =>
    (hcont.measurable.comp (hYm.add measurable_const)).aestronglyMeasurable
  have hdiff : Integrable (fun D => q0 M (yPlusL v 0 D + z₂) - q0 M (yPlusL v 0 D + z₁)) ν := by
    refine (integrable_const ((|M.c - M.p| + |M.h + M.p|) * |z₂ - z₁|)).mono'
      ((hfm z₂).sub (hfm z₁)) (Filter.Eventually.of_forall (fun D => ?_))
    rw [Real.norm_eq_abs]
    have := c47_q0_lip M hM.integrable (yPlusL v 0 D + z₂) (yPlusL v 0 D + z₁)
    rwa [show yPlusL v 0 D + z₂ - (yPlusL v 0 D + z₁) = z₂ - z₁ by ring] at this
  unfold q
  rw [hf z₁, hf z₂]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hM.hγ0.le L)
  by_cases hi : Integrable (fun D => q0 M (yPlusL v 0 D + z₁)) ν
  · have hi2 : Integrable (fun D => q0 M (yPlusL v 0 D + z₂)) ν := by
      refine (hi.add hdiff).congr (Filter.Eventually.of_forall (fun D => ?_))
      simp
    rw [← sub_nonneg, ← integral_sub hi2 hi]
    have hT := c47_intT_le M hM v z₁ hb
    have hTi := c47_int_tail M (fun D => yPlusL v 0 D + z₁) (hYm.add measurable_const)
    have hlow : ∫ D, (z₂ - z₁) * ((M.c + M.h) - (M.p + M.h)
          * (M.μ (Set.Ioi (yPlusL v 0 D + z₁))).toReal) ∂ν
        ≤ ∫ D, (q0 M (yPlusL v 0 D + z₂) - q0 M (yPlusL v 0 D + z₁)) ∂ν := by
      refine integral_mono (((integrable_const (M.c + M.h)).sub
        (hTi.const_mul (M.p + M.h))).const_mul (z₂ - z₁)) hdiff (fun D => ?_)
      have := c47_q0_diff M hM.integrable hph
        (show yPlusL v 0 D + z₁ ≤ yPlusL v 0 D + z₂ by linarith)
      rwa [show yPlusL v 0 D + z₂ - (yPlusL v 0 D + z₁) = z₂ - z₁ by ring] at this
    rw [integral_const_mul, integral_sub (integrable_const _) (hTi.const_mul _),
      integral_const_mul, integral_const] at hlow
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hlow
    have hθ : (M.p + M.h) * θbar M = M.c + M.h := by
      unfold θbar; field_simp
    have h3 : 0 ≤ (z₂ - z₁) * ((M.c + M.h) - (M.p + M.h)
        * ∫ D, (M.μ (Set.Ioi (yPlusL v 0 D + z₁))).toReal ∂ν) := by
      apply mul_nonneg (by linarith)
      have := mul_le_mul_of_nonneg_left hT hph.le
      linarith
    linarith
  · have hi2 : ¬ Integrable (fun D => q0 M (yPlusL v 0 D + z₂)) ν := by
      intro h2
      apply hi
      refine (h2.sub hdiff).congr (Filter.Eventually.of_forall (fun D => ?_))
      simp
    rw [integral_undef hi, integral_undef hi2]

/-! ## Child A: continuity of `gB` in the order quantity -/

theorem c47_int_diff_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (F G : α → ℝ) (hF : AEStronglyMeasurable F μ) (hG : AEStronglyMeasurable G μ) (c : ℝ)
    (hc : 0 ≤ c) (h : ∀ x, |F x - G x| ≤ c) : |∫ x, F x ∂μ - ∫ x, G x ∂μ| ≤ c := by
  have hd : Integrable (fun x => F x - G x) μ :=
    (integrable_const c).mono' (hF.sub hG) (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs]; exact h x))
  by_cases hFi : Integrable F μ
  · have hGi : Integrable G μ :=
      (hFi.sub hd).congr (Filter.Eventually.of_forall (fun x => by simp))
    rw [← integral_sub hFi hGi]
    have := norm_integral_le_of_norm_le_const (μ := μ) (C := c) (f := fun x => F x - G x)
      (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact h x))
    simpa [Real.norm_eq_abs] using this
  · have hGi : ¬ Integrable G μ := fun hGi =>
      hFi ((hGi.add hd).congr (Filter.Eventually.of_forall (fun x => by simp)))
    rw [integral_undef hFi, integral_undef hGi]
    simpa using hc

theorem c47_int_ge {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α → ℝ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ x, -B ≤ F x) : -B ≤ ∫ x, F x ∂μ := by
  by_cases hFi : Integrable F μ
  · have := integral_mono (integrable_const (-B)) hFi h
    simpa using this
  · rw [integral_undef hFi]; linarith

theorem c47_vext_lip {L : ℕ} (v v' : Fin L → ℝ) (l : ℕ) : |vext v l - vext v' l| ≤ ‖v - v'‖ := by
  by_cases h : l < L
  · simp only [vext, h, dif_pos]
    have := norm_le_pi_norm (v - v') ⟨l, h⟩
    simpa [Real.norm_eq_abs] using this
  · simp [vext, h]

theorem c47_onHand_lip {L : ℕ} (v v' : Fin L → ℝ) (z : ℝ) (D : Fin L → ℝ) :
    ∀ j : ℕ, |onHand v z D j - onHand v' z D j| ≤ 2 * ((j : ℝ) + 1) * ‖v - v'‖ := by
  have hN := norm_nonneg (v - v')
  have harr : ∀ j, |arrival v z j - arrival v' z j| ≤ 2 * ‖v - v'‖ := by
    intro j
    unfold arrival
    split_ifs
    · unfold xext
      have h1 := c47_vext_lip v v' j
      have h2 := c47_vext_lip v v' (j + 1)
      rw [abs_le]
      constructor <;> linarith [le_abs_self (vext v j - vext v' j),
        neg_abs_le (vext v j - vext v' j), le_abs_self (vext v (j + 1) - vext v' (j + 1)),
        neg_abs_le (vext v (j + 1) - vext v' (j + 1))]
    · simp
  intro j
  induction j with
  | zero =>
    simp only [onHand]
    have := harr 0
    push_cast; linarith
  | succ j ih =>
    simp only [onHand]
    have h1 := abs_max_sub_max_le_abs (onHand v z D j - vext D j) (onHand v' z D j - vext D j) 0
    rw [show onHand v z D j - vext D j - (onHand v' z D j - vext D j)
      = onHand v z D j - onHand v' z D j by ring] at h1
    have h2 := harr (j + 1)
    have e : 2 * (((j + 1 : ℕ) : ℝ) + 1) * ‖v - v'‖
        = 2 * ((j : ℝ) + 1) * ‖v - v'‖ + 2 * ‖v - v'‖ := by push_cast; ring
    rw [e, abs_le]
    set m := max (onHand v z D j - vext D j) 0 - max (onHand v' z D j - vext D j) 0
    have hm : max (onHand v z D j - vext D j) 0 - max (onHand v' z D j - vext D j) 0 = m := rfl
    constructor <;> linarith [le_abs_self m, neg_abs_le m,
      le_abs_self (arrival v z (j + 1) - arrival v' z (j + 1)),
      neg_abs_le (arrival v z (j + 1) - arrival v' z (j + 1)),
      le_abs_self (onHand v z D j - onHand v' z D j), neg_abs_le (onHand v z D j - onHand v' z D j)]

theorem c47_nextZ_lip {L : ℕ} (v v' : Fin L → ℝ) (d z : ℝ) :
    ‖nextZ v d z - nextZ v' d z‖ ≤ 3 * ‖v - v'‖ := by
  have hN := norm_nonneg (v - v')
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun l => ?_)
  rw [Real.norm_eq_abs, Pi.sub_apply]
  simp only [nextZ]
  have h0 := c47_vext_lip v v' 0
  have h1 := c47_vext_lip v v' 1
  have hl := c47_vext_lip v v' ((l : ℕ) + 1)
  set a := vext v 0 - vext v 1 - d
  set a' := vext v' 0 - vext v' 1 - d
  have hm := abs_max_sub_max_le_abs a a' 0
  have ha : a - a' = (vext v 0 - vext v' 0) - (vext v 1 - vext v' 1) := by
    simp only [a, a']; ring
  have haa : |a - a'| ≤ 2 * ‖v - v'‖ := by
    rw [ha, abs_le]
    constructor <;> linarith [le_abs_self (vext v 0 - vext v' 0),
      neg_abs_le (vext v 0 - vext v' 0), le_abs_self (vext v 1 - vext v' 1),
      neg_abs_le (vext v 1 - vext v' 1)]
  split_ifs
  · rw [abs_le]
    constructor <;> linarith [le_abs_self (max a 0 - max a' 0), neg_abs_le (max a 0 - max a' 0),
      le_abs_self (vext v (↑l + 1) - vext v' (↑l + 1)),
      neg_abs_le (vext v (↑l + 1) - vext v' (↑l + 1))]
  · rw [abs_le]
    constructor <;> linarith [le_abs_self (vext v (↑l + 1) - vext v' (↑l + 1)),
      neg_abs_le (vext v (↑l + 1) - vext v' (↑l + 1))]

theorem c47_nextZ_z {L : ℕ} (v : Fin L → ℝ) (d z z' : ℝ) :
    ‖nextZ v d z - nextZ v d z'‖ ≤ |z - z'| := by
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr (fun l => ?_)
  rw [Real.norm_eq_abs, Pi.sub_apply]
  simp only [nextZ]
  apply le_of_eq; congr 1; ring

theorem c47_nextZ_cont {L : ℕ} (v : Fin L → ℝ) (z : ℝ) : Continuous (fun d => nextZ v d z) := by
  apply continuous_pi
  intro l
  simp only [nextZ]
  split_ifs
  · exact (((continuous_const.sub continuous_id).max continuous_const).add continuous_const).add
      continuous_const
  · exact continuous_const

theorem c47_q0_low (M : Data) (hM : ∀ _ : Unit, True) [IsProbabilityMeasure M.μ]
    (hint : Integrable id M.μ) (hph : 0 < M.p + M.h) (hch : 0 < M.c + M.h) {y : ℝ} (hy : 0 ≤ y) :
    -(|M.h| * |∫ d, d ∂M.μ|) ≤ q0 M y := by
  rw [c47_q0_repr M hint y]
  have hA : y - ∫ d, d ∂M.μ ≤ ∫ d, max (y - d) 0 ∂M.μ := by
    have h1 : ∫ d, (y - d) ∂M.μ = y - ∫ d, d ∂M.μ := by
      rw [show (∫ d, (y - d) ∂M.μ) = ∫ _d, y ∂M.μ - ∫ d, d ∂M.μ from
        integral_sub (integrable_const y) hint]
      simp
    rw [← h1]
    exact integral_mono ((integrable_const y).sub hint)
      (((integrable_const y).sub hint).pos_part) (fun d => le_max_left _ _)
  have h2 := mul_le_mul_of_nonneg_left hA hph.le
  have h3 : -(|M.h| * |∫ d, d ∂M.μ|) ≤ -(M.h * ∫ d, d ∂M.μ) := by
    rw [neg_le_neg_iff, ← abs_mul]; exact le_abs_self _
  have h4 : 0 ≤ (M.c + M.h) * y := mul_nonneg hch.le hy
  nlinarith

theorem c47_q_low {L : ℕ} (M : Data) (hM : Assumptions L M) (v : Fin L → ℝ) {z : ℝ}
    (hz : 0 ≤ z) : -(M.γ ^ L * (|M.h| * |∫ d, d ∂M.μ|)) ≤ q M v z := by
  haveI := hM.prob
  have hph : 0 < M.p + M.h := lt_trans hM.hch hM.hph
  unfold q
  rw [← mul_neg]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hM.hγ0.le L)
  apply c47_int_ge _ _ _ (by positivity)
  intro D
  apply c47_q0_low M (fun _ => trivial) hM.integrable hph hM.hch
  rw [c47_yPlusL_z hM.hL]
  have := c47_yPlusL_nonneg hM.hL v D
  linarith

theorem c47_q_lip_v {L : ℕ} (M : Data) (hM : Assumptions L M) (v v' : Fin L → ℝ) (z : ℝ) :
    |q M v z - q M v' z|
      ≤ M.γ ^ L * ((|M.c - M.p| + |M.h + M.p|) * (2 * ((L : ℝ) + 1) * ‖v - v'‖)) := by
  haveI := hM.prob
  have hcont := c47_q0_cont M hM.integrable
  unfold q
  rw [← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg hM.hγ0.le L)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hM.hγ0.le L)
  apply c47_int_diff_le _ _ _
    ((hcont.measurable.comp (c47_onHand_meas v z L)).aestronglyMeasurable)
    ((hcont.measurable.comp (c47_onHand_meas v' z L)).aestronglyMeasurable) _ (by positivity)
  intro D
  exact le_trans (c47_q0_lip M hM.integrable _ _)
    (mul_le_mul_of_nonneg_left (c47_onHand_lip v v' z D L) (by positivity))

theorem c47_fB_props {L : ℕ} (M : Data) (hM : Assumptions L M) (k : ℕ) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ (∀ w : Fin L → ℝ, -B ≤ fB M k w) ∧
      (∀ w w' : Fin L → ℝ, |fB M k w - fB M k w'| ≤ C * ‖w - w'‖) := by
  haveI := hM.prob
  haveI : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.mem_Ici.mpr le_rfl⟩⟩
  have hγ := hM.hγ0
  induction k with
  | zero => exact ⟨0, 0, le_refl _, le_refl _, fun w => by simp [fB], fun w w' => by simp [fB]⟩
  | succ k ih =>
    obtain ⟨B, C, hB, hC, hlow, hlip⟩ := ih
    set Bq := M.γ ^ L * (|M.h| * |∫ d, d ∂M.μ|) with hBq
    set Kq := M.γ ^ L * ((|M.c - M.p| + |M.h + M.p|) * (2 * ((L : ℝ) + 1))) with hKq
    have hBq0 : 0 ≤ Bq := by positivity
    have hKq0 : 0 ≤ Kq := by positivity
    have hfc : Continuous (fB (L := L) M k) := by
      have : LipschitzWith ⟨C, hC⟩ (fB (L := L) M k) := LipschitzWith.of_dist_le_mul (fun a b => by
        rw [Real.dist_eq, dist_eq_norm]; exact hlip a b)
      exact this.continuous
    have hglow : ∀ (w : Fin L → ℝ) (z : Set.Ici (0 : ℝ)), -(Bq + M.γ * B) ≤ gB M k w z := by
      intro w z
      unfold gB gstep
      have h1 := c47_q_low M hM w z.2
      have h2 := c47_int_ge M.μ (fun d => fB M k (nextZ w d z)) B hB (fun d => hlow _)
      nlinarith
    have hglip : ∀ (w w' : Fin L → ℝ) (z : ℝ), |gB M k w z - gB M k w' z| ≤ (Kq + M.γ * (C * 3)) * ‖w - w'‖ := by
      intro w w' z
      unfold gB gstep
      have h1 := c47_q_lip_v M hM w w' z
      have h2 := c47_int_diff_le M.μ (fun d => fB M k (nextZ w d z))
        (fun d => fB M k (nextZ w' d z)) (hfc.comp (c47_nextZ_cont w z)).aestronglyMeasurable
        (hfc.comp (c47_nextZ_cont w' z)).aestronglyMeasurable (C * (3 * ‖w - w'‖))
        (by positivity) (fun d => le_trans (hlip _ _)
          (mul_le_mul_of_nonneg_left (c47_nextZ_lip w w' d z) hC))
      calc _ = |(q M w z - q M w' z) + M.γ * (∫ d, fB M k (nextZ w d z) ∂M.μ
              - ∫ d, fB M k (nextZ w' d z) ∂M.μ)| := by congr 1; ring
        _ ≤ |q M w z - q M w' z| + |M.γ * (∫ d, fB M k (nextZ w d z) ∂M.μ
              - ∫ d, fB M k (nextZ w' d z) ∂M.μ)| := abs_add_le _ _
        _ = |q M w z - q M w' z| + M.γ * |∫ d, fB M k (nextZ w d z) ∂M.μ
              - ∫ d, fB M k (nextZ w' d z) ∂M.μ| := by rw [abs_mul, abs_of_pos hγ]
        _ ≤ M.γ ^ L * ((|M.c - M.p| + |M.h + M.p|) * (2 * ((L : ℝ) + 1) * ‖w - w'‖))
              + M.γ * (C * (3 * ‖w - w'‖)) :=
            add_le_add h1 (mul_le_mul_of_nonneg_left h2 hγ.le)
        _ = _ := by rw [hKq]; ring
    have hbdd : ∀ w : Fin L → ℝ, BddBelow (Set.range (fun z : Set.Ici (0 : ℝ) => gB M k w z)) := fun w =>
      ⟨-(Bq + M.γ * B), fun _ ⟨z, hz⟩ => hz ▸ hglow w z⟩
    refine ⟨Bq + M.γ * B, Kq + M.γ * (C * 3), by positivity, by positivity, ?_, ?_⟩
    · intro w
      rw [fB_succ]
      exact le_ciInf (fun z => hglow w z)
    · have key : ∀ w w' : Fin L → ℝ, fB M (k + 1) w - (Kq + M.γ * (C * 3)) * ‖w - w'‖ ≤ fB M (k + 1) w' := by
        intro w w'
        rw [fB_succ, fB_succ]
        refine le_ciInf (fun z => ?_)
        have h1 := ciInf_le (hbdd w) z
        have h2 := hglip w w' z
        rw [abs_le] at h2
        linarith [h2.1]
      intro w w'
      have h1 := key w w'
      have h2 := key w' w
      rw [norm_sub_rev w' w] at h2
      rw [abs_le]; constructor <;> linarith


/-! S2 Fubini core: one period of the on-hand recursion peeled off as a single integral. -/

theorem c47f_vext_nextZ {L : ℕ} (Y : Fin L → ℝ) (d z : ℝ) (i : ℕ) (hi : i < L) :
    vext (nextZ Y d z) i
      = (if i = 0 then max (vext Y 0 - vext Y 1 - d) 0 else 0) + vext Y (i + 1) + z := by
  simp [vext, hi, nextZ]

theorem c47f_vext_ge {L : ℕ} (Y : Fin L → ℝ) (i : ℕ) (hi : L ≤ i) : vext Y i = 0 := by
  simp [vext, show ¬ i < L by omega]

theorem c47f_arr {L : ℕ} (Y : Fin L → ℝ) (d z : ℝ) (i : ℕ) (h1 : 1 ≤ i) (hi : i < L) :
    arrival (nextZ Y d z) 0 i = arrival Y z (i + 1) := by
  have hne : i ≠ 0 := by omega
  simp only [arrival, hi, if_true, xext]
  rw [c47f_vext_nextZ Y d z i hi, if_neg hne]
  by_cases h2 : i + 1 < L
  · rw [c47f_vext_nextZ Y d z (i + 1) h2, if_neg (by omega), if_pos h2]; ring
  · rw [c47f_vext_ge (nextZ Y d z) (i + 1) (by omega), if_neg h2,
      c47f_vext_ge Y (i + 1) (by omega)]; ring

/-- Pointwise shift: the first period of `onHand` is the transition `nextZ`. -/
theorem c47f_onHand_shift {L : ℕ} (Y : Fin L → ℝ) (z : ℝ) (D D' : Fin L → ℝ) :
    ∀ j, j < L → (∀ i, i < j → vext D (i + 1) = vext D' i) →
      onHand Y z D (j + 1) = onHand (nextZ Y (vext D 0) z) 0 D' j := by
  intro j
  induction j with
  | zero =>
    intro hj _
    have e1 : onHand Y z D (0 + 1) = max (arrival Y z 0 - vext D 0) 0 + arrival Y z 1 := rfl
    have e2 : onHand (nextZ Y (vext D 0) z) 0 D' 0 = arrival (nextZ Y (vext D 0) z) 0 0 := rfl
    rw [e1, e2]
    simp only [arrival, hj, if_true, xext]
    rw [c47f_vext_nextZ Y _ z 0 hj, if_pos rfl]
    by_cases h1 : 1 < L
    · rw [c47f_vext_nextZ Y _ z 1 h1, if_neg one_ne_zero, if_pos h1]; ring
    · rw [if_neg h1, c47f_vext_ge (nextZ Y (vext D 0) z) 1 (by omega),
        c47f_vext_ge Y 1 (by omega)]; ring
  | succ j ih =>
    intro hj hD
    have ih' := ih (by omega) (fun i hi => hD i (by omega))
    have e1 : onHand Y z D (j + 1 + 1)
        = max (onHand Y z D (j + 1) - vext D (j + 1)) 0 + arrival Y z (j + 1 + 1) := rfl
    have e2 : onHand (nextZ Y (vext D 0) z) 0 D' (j + 1)
        = max (onHand (nextZ Y (vext D 0) z) 0 D' j - vext D' j) 0
          + arrival (nextZ Y (vext D 0) z) 0 (j + 1) := rfl
    rw [e1, e2, ih', hD j (by omega), c47f_arr Y _ z (j + 1) (by omega) hj]

theorem c47f_vext_meas {L : ℕ} (j : ℕ) : Measurable (fun D : Fin L → ℝ => vext D j) := by
  by_cases h : j < L
  · simp only [vext, h, dif_pos]; exact measurable_pi_apply _
  · simp only [vext, h, dif_neg, not_false_eq_true]; exact measurable_const

theorem c47f_onHand_meas {L : ℕ} (v : Fin L → ℝ) (z : ℝ) :
    ∀ j, Measurable (fun D : Fin L → ℝ => onHand v z D j) := by
  intro j
  induction j with
  | zero => simp only [onHand]; exact measurable_const
  | succ j ih =>
    simp only [onHand]
    exact ((ih.sub (c47f_vext_meas j)).max measurable_const).add measurable_const

theorem c47f_onHand_bound {L : ℕ} (Y : Fin L → ℝ) (z : ℝ) :
    ∀ j, ∃ C : ℝ, ∀ D : Fin L → ℝ, |onHand Y z D j| ≤ C + ∑ i ∈ Finset.range j, |vext D i| := by
  intro j
  induction j with
  | zero => exact ⟨|arrival Y z 0|, fun D => by simp [onHand]⟩
  | succ j ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C + |arrival Y z (j + 1)|, fun D => ?_⟩
    have e : onHand Y z D (j + 1) = max (onHand Y z D j - vext D j) 0 + arrival Y z (j + 1) := rfl
    rw [e, Finset.sum_range_succ]
    have h1 : |max (onHand Y z D j - vext D j) 0| ≤ |onHand Y z D j| + |vext D j| := by
      rw [abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (by positivity)
      calc onHand Y z D j - vext D j ≤ |onHand Y z D j - vext D j| := le_abs_self _
        _ ≤ |onHand Y z D j| + |vext D j| := abs_sub _ _
    have h2 := hC D
    calc _ ≤ |max (onHand Y z D j - vext D j) 0| + |arrival Y z (j + 1)| := abs_add_le _ _
      _ ≤ _ := by linarith

theorem c47f_int_vext {L : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (hint : Integrable id μ)
    (i : ℕ) : Integrable (fun D : Fin L → ℝ => vext D i) (Measure.pi fun _ : Fin L => μ) := by
  by_cases h : i < L
  · simp only [vext, h, dif_pos]
    exact (measurePreserving_eval (fun _ : Fin L => μ) ⟨i, h⟩).integrable_comp_of_integrable hint
  · simp only [vext, h, dif_neg, not_false_eq_true]; exact integrable_const _

theorem c47f_int_phi {L : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (hint : Integrable id μ)
    (φ : ℝ → ℝ) (hφ : Continuous φ) (A B : ℝ) (hB : 0 ≤ B) (hφb : ∀ y, |φ y| ≤ A + B * |y|)
    (Y : Fin L → ℝ) (z : ℝ) (j : ℕ) :
    Integrable (fun D => φ (onHand Y z D j)) (Measure.pi fun _ : Fin L => μ) := by
  obtain ⟨C, hC⟩ := c47f_onHand_bound Y z j
  have hsum : Integrable (fun D : Fin L → ℝ =>
      A + B * (C + ∑ i ∈ Finset.range j, |vext D i|)) (Measure.pi fun _ : Fin L => μ) :=
    (integrable_const A).add (((integrable_const C).add (integrable_finsetSum _
      (fun i _ => (c47f_int_vext μ hint i).abs))).const_mul B)
  refine hsum.mono' (hφ.measurable.comp (c47f_onHand_meas Y z j)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun D => ?_)
  rw [Real.norm_eq_abs]
  exact le_trans (hφb _) (by gcongr; exact hC D)

theorem c47f_ins0 {m : ℕ} (d : ℝ) (T : Fin m → ℝ) (i : ℕ) (hi : i < m) :
    vext (Fin.insertNth (α := fun _ => ℝ) (0 : Fin (m + 1)) d T) (i + 1) = T ⟨i, hi⟩ := by
  have hs : (⟨i + 1, by omega⟩ : Fin (m + 1)) = (0 : Fin (m + 1)).succAbove ⟨i, hi⟩ := by
    ext; simp
  simp only [vext, show i + 1 < m + 1 by omega, dif_pos]
  rw [hs, Fin.insertNth_apply_succAbove]

theorem c47f_ins0' {m : ℕ} (d : ℝ) (T : Fin m → ℝ) :
    vext (Fin.insertNth (α := fun _ => ℝ) (0 : Fin (m + 1)) d T) 0 = d := by
  simp [vext]

theorem c47f_insl {m : ℕ} (a : ℝ) (T : Fin m → ℝ) (i : ℕ) (hi : i < m) :
    vext (Fin.insertNth (α := fun _ => ℝ) (Fin.last m) a T) i = T ⟨i, hi⟩ := by
  have hs : (⟨i, by omega⟩ : Fin (m + 1)) = (Fin.last m).succAbove ⟨i, hi⟩ := by
    ext; simp [Fin.succAbove_last]
  simp only [vext, show i < m + 1 by omega, dif_pos]
  rw [hs, Fin.insertNth_apply_succAbove]

/-- CORE: `E φ(y_{j+1}) = E_d E φ(y_j(next state))`. -/
theorem c47f_core {m : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (hint : Integrable id μ)
    (φ : ℝ → ℝ) (hφ : Continuous φ) (A B : ℝ) (hB : 0 ≤ B) (hφb : ∀ y, |φ y| ≤ A + B * |y|)
    (Y : Fin (m + 1) → ℝ) (z : ℝ) (j : ℕ) (hj : j ≤ m) :
    ∫ D, φ (onHand Y z D (j + 1)) ∂(Measure.pi fun _ : Fin (m + 1) => μ)
      = ∫ d, (∫ D', φ (onHand (nextZ Y d z) 0 D' j)
          ∂(Measure.pi fun _ : Fin (m + 1) => μ)) ∂μ := by
  have h0 := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0
  have hl := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) (Fin.last m)
  have key : ∀ (d a : ℝ) (T : Fin m → ℝ),
      φ (onHand (nextZ Y d z) 0
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm (a, T)) j)
        = φ (onHand Y z
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm (d, T)) (j + 1)) := by
    intro d a T
    have hs0 : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm (d, T)
        = Fin.insertNth (α := fun _ => ℝ) 0 d T := rfl
    have hsl : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm (a, T)
        = Fin.insertNth (α := fun _ => ℝ) (Fin.last m) a T := rfl
    rw [hs0, hsl]
    have hd := c47f_ins0' d T
    conv_rhs => rw [c47f_onHand_shift Y z _
      (Fin.insertNth (α := fun _ => ℝ) (Fin.last m) a T) j (by omega) (fun i hi => by
        rw [c47f_ins0 d T i (by omega), c47f_insl a T i (by omega)]), hd]
  have hin : ∀ d, ∫ D', φ (onHand (nextZ Y d z) 0 D' j) ∂(Measure.pi fun _ : Fin (m + 1) => μ)
      = ∫ T, φ (onHand Y z
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm (d, T)) (j + 1))
          ∂(Measure.pi fun _ : Fin m => μ) := by
    intro d
    rw [← hl.symm.integral_comp']
    have : ∀ p : ℝ × (Fin m → ℝ), φ (onHand (nextZ Y d z) 0
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm p) j)
        = (fun T => φ (onHand Y z
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm (d, T)) (j + 1))) p.2 :=
      fun p => key d p.1 p.2
    simp_rw [this]
    rw [integral_fun_snd (μ := μ) (fun T => φ (onHand Y z
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm (d, T)) (j + 1)))]
    simp
  have hI : Integrable (fun p => φ (onHand Y z
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm p) (j + 1)))
      (μ.prod (Measure.pi fun _ : Fin m => μ)) :=
    h0.symm.integrable_comp_of_integrable (c47f_int_phi μ hint φ hφ A B hB hφb Y z (j + 1))
  rw [← h0.symm.integral_comp']
  rw [integral_prod _ hI]
  exact integral_congr_ae (Filter.Eventually.of_forall fun d => (hin d).symm)


/-- Child A: `gB` is (Lipschitz) continuous in the order quantity. -/
theorem childA_gB_continuousOn {L : ℕ} (M : Data) (hM : Assumptions L M) (k : ℕ)
    (v : Fin L → ℝ) (hv : v ∈ ZipkinLostSales.LNatural.V L) :
    ContinuousOn (gB M k v) (Set.Ici 0) := by
  haveI := hM.prob
  have hγ := hM.hγ0
  obtain ⟨B, C, hB, hC, hlow, hlip⟩ := c47_fB_props M hM k
  have hfc : Continuous (fB (L := L) M k) := by
    have : LipschitzWith ⟨C, hC⟩ (fB (L := L) M k) := LipschitzWith.of_dist_le_mul (fun a b => by
      rw [Real.dist_eq, dist_eq_norm]; exact hlip a b)
    exact this.continuous
  have hcont := c47_q0_cont M hM.integrable
  set K := |M.c - M.p| + |M.h + M.p| with hK
  have hK0 : 0 ≤ K := by positivity
  have hL : LipschitzWith ⟨M.γ ^ L * K + M.γ * C, by positivity⟩ (gB M k v) := by
    apply LipschitzWith.of_dist_le_mul
    intro z z'
    rw [Real.dist_eq, Real.dist_eq]
    show |gB M k v z - gB M k v z'| ≤ (M.γ ^ L * K + M.γ * C) * |z - z'|
    unfold gB gstep
    have h1 : |q M v z - q M v z'| ≤ M.γ ^ L * (K * |z - z'|) := by
      unfold q
      rw [← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg hγ.le L)]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hγ.le L)
      apply c47_int_diff_le _ _ _
        ((hcont.measurable.comp (c47_onHand_meas v z L)).aestronglyMeasurable)
        ((hcont.measurable.comp (c47_onHand_meas v z' L)).aestronglyMeasurable) _ (by positivity)
      intro D
      show |q0 M (yPlusL v z D) - q0 M (yPlusL v z' D)| ≤ K * |z - z'|
      rw [c47_yPlusL_z hM.hL v z D, c47_yPlusL_z hM.hL v z' D]
      have := c47_q0_lip M hM.integrable (yPlusL v 0 D + z) (yPlusL v 0 D + z')
      rwa [show yPlusL v 0 D + z - (yPlusL v 0 D + z') = z - z' by ring] at this
    have h2 := c47_int_diff_le M.μ (fun d => fB M k (nextZ v d z))
      (fun d => fB M k (nextZ v d z')) (hfc.comp (c47_nextZ_cont v z)).aestronglyMeasurable
      (hfc.comp (c47_nextZ_cont v z')).aestronglyMeasurable (C * |z - z'|) (by positivity)
      (fun d => le_trans (hlip _ _) (mul_le_mul_of_nonneg_left (c47_nextZ_z v d z z') hC))
    calc _ = |(q M v z - q M v z') + M.γ * (∫ d, fB M k (nextZ v d z) ∂M.μ
            - ∫ d, fB M k (nextZ v d z') ∂M.μ)| := by congr 1; ring
      _ ≤ |q M v z - q M v z'| + |M.γ * (∫ d, fB M k (nextZ v d z) ∂M.μ
            - ∫ d, fB M k (nextZ v d z') ∂M.μ)| := abs_add_le _ _
      _ = |q M v z - q M v z'| + M.γ * |∫ d, fB M k (nextZ v d z) ∂M.μ
            - ∫ d, fB M k (nextZ v d z') ∂M.μ| := by rw [abs_mul, abs_of_pos hγ]
      _ ≤ M.γ ^ L * (K * |z - z'|) + M.γ * (C * |z - z'|) :=
          add_le_add h1 (mul_le_mul_of_nonneg_left h2 hγ.le)
      _ = _ := by ring
  exact hL.continuous.continuousOn

/-! ## Child C from the open key lemma D, and the parent modulo D -/

theorem c47_nextZ_mem_V {L : ℕ} (v : Fin L → ℝ) (hv : v ∈ ZipkinLostSales.LNatural.V L) (d : ℝ)
    {z : ℝ} (hz : 0 ≤ z) : nextZ v d z ∈ ZipkinLostSales.LNatural.V L := by
  obtain ⟨hanti, hnn⟩ := hv
  have hvext_nn : ∀ l, 0 ≤ vext v l := fun l => by
    unfold vext; split_ifs
    · exact hnn _
    · exact le_refl 0
  have hvext_anti : ∀ a b : ℕ, a ≤ b → vext v b ≤ vext v a := by
    intro a b hab
    unfold vext
    split_ifs with h1 h2 h2
    · exact hanti (Fin.mk_le_mk.mpr hab)
    · omega
    · exact hnn _
    · exact le_refl 0
  refine ⟨fun a b hab => ?_, fun l => ?_⟩
  · simp only [nextZ]
    have := hvext_anti ((a : ℕ) + 1) ((b : ℕ) + 1) (by have : (a : ℕ) ≤ b := hab; omega)
    split_ifs with hb ha <;> first
      | linarith [this, le_max_right (vext v 0 - vext v 1 - d) 0]
      | (exfalso; have : (a : ℕ) ≤ b := hab; omega)
  · simp only [nextZ]
    split_ifs <;> linarith [le_max_right (vext v 0 - vext v 1 - d) 0, hvext_nn ((l : ℕ) + 1)]

theorem childC_of_D {L : ℕ} (M : Data) (hM : Assumptions L M) (k : ℕ)
    (hD : ∀ w w' : Fin L → ℝ, w ∈ ZipkinLostSales.LNatural.V L →
      w' - w ∈ ZipkinLostSales.LNatural.V L → fB M k w ≤ fB M k w')
    (v : Fin L → ℝ) (hv : v ∈ ZipkinLostSales.LNatural.V L) (z₁ z₂ : ℝ) (h0 : 0 ≤ z₁)
    (h12 : z₁ ≤ z₂) :
    ∫ d, fB M k (nextZ v d z₁) ∂M.μ ≤ ∫ d, fB M k (nextZ v d z₂) ∂M.μ := by
  haveI := hM.prob
  obtain ⟨B, C, hB, hC, hlow, hlip⟩ := c47_fB_props M hM k
  have hfc : Continuous (fB (L := L) M k) := by
    have : LipschitzWith ⟨C, hC⟩ (fB (L := L) M k) := LipschitzWith.of_dist_le_mul (fun a b => by
      rw [Real.dist_eq, dist_eq_norm]; exact hlip a b)
    exact this.continuous
  have hpt : ∀ d, fB M k (nextZ v d z₁) ≤ fB M k (nextZ v d z₂) := by
    intro d
    apply hD _ _ (c47_nextZ_mem_V v hv d h0)
    have he : nextZ v d z₂ - nextZ v d z₁ = fun _ => z₂ - z₁ := by
      funext l; simp only [Pi.sub_apply, nextZ]; ring
    rw [he]
    exact ⟨fun _ _ _ => le_refl _, fun _ => by linarith⟩
  have hdiff : Integrable (fun d => fB M k (nextZ v d z₂) - fB M k (nextZ v d z₁)) M.μ := by
    refine (integrable_const (C * |z₂ - z₁|)).mono'
      (((hfc.comp (c47_nextZ_cont v z₂)).sub (hfc.comp (c47_nextZ_cont v z₁))).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun d => ?_))
    rw [Real.norm_eq_abs]
    exact le_trans (hlip _ _) (mul_le_mul_of_nonneg_left (c47_nextZ_z v d z₂ z₁) hC)
  by_cases hi : Integrable (fun d => fB M k (nextZ v d z₁)) M.μ
  · have hi2 : Integrable (fun d => fB M k (nextZ v d z₂)) M.μ :=
      (hi.add hdiff).congr (Filter.Eventually.of_forall (fun d => by simp))
    exact integral_mono hi hi2 hpt
  · have hi2 : ¬ Integrable (fun d => fB M k (nextZ v d z₂)) M.μ := fun h2 =>
      hi ((h2.sub hdiff).congr (Filter.Eventually.of_forall (fun d => by simp)))
    rw [integral_undef hi, integral_undef hi2]
/-- The fractiles are nonnegative: for `s < 0` the tail probability is `1 > θ̄`. -/
theorem sbar_nonneg {L : ℕ} (M : Data) (hM : Assumptions L M) (l : Fin (L + 1)) :
    0 ≤ sbar L M l := by
  apply Real.sInf_nonneg
  intro s hs
  by_contra hneg
  push_neg at hneg
  simp only [Set.mem_setOf_eq] at hs
  haveI := hM.prob
  have hθ : θbar M < 1 := by
    unfold θbar
    have hph : 0 < M.p + M.h := lt_trans hM.hch hM.hph
    rw [div_lt_one hph]; exact hM.hph
  have hnull : ∀ j : Fin (L + 1),
      (Measure.pi fun _ : Fin (L + 1) => M.μ) {D | D j < 0} = 0 := by
    intro j
    have := Measure.pi_eval_preimage_null (fun _ : Fin (L + 1) => M.μ) (i := j)
      (s := Set.Iio 0) hM.demand_nonneg
    simpa [Set.preimage, Set.mem_Iio] using this
  have hcompl : (Measure.pi fun _ : Fin (L + 1) => M.μ)
      {D | s < ∑ j ∈ Finset.Ici l, D j}ᶜ = 0 := by
    apply measure_mono_null _ (measure_iUnion_null hnull)
    intro D hD
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hD
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra h
    push_neg at h
    have : 0 ≤ ∑ j ∈ Finset.Ici l, D j := Finset.sum_nonneg (fun j _ => h j)
    linarith
  have h1 : (Measure.pi fun _ : Fin (L + 1) => M.μ) {D | s < ∑ j ∈ Finset.Ici l, D j} = 1 := by
    rw [measure_congr (ae_eq_univ.mpr hcompl), measure_univ]
  rw [h1] at hs
  simp at hs
  linarith

/-- Assembly: the parent follows from continuity (A), the monotonicity of `q` beyond the
Karlin–Scarf–Morton bound (B) and the monotonicity of the continuation in `z` (C). -/
theorem assembly {L : ℕ} (M : Data) (hM : Assumptions L M) (k : ℕ) (v : Fin L → ℝ)
    (hv : v ∈ ZipkinLostSales.LNatural.V L)
    (hA : ContinuousOn (gB M k v) (Set.Ici 0))
    (hB : ∀ z₁ z₂ : ℝ, 0 ≤ z₁ → z₁ ≤ z₂ →
      (sbar L M (Fin.last L) ≤ z₁ ∨ ∃ l : Fin L, sbar L M l.castSucc ≤ v l + z₁) →
      q M v z₁ ≤ q M v z₂)
    (hC : ∀ z₁ z₂ : ℝ, 0 ≤ z₁ → z₁ ≤ z₂ →
      ∫ d, fB M k (nextZ v d z₁) ∂M.μ ≤ ∫ d, fB M k (nextZ v d z₂) ∂M.μ) :
    ∃ z : ℝ, IsOptOrder M k v z ∧ InZ L M v z := by
  classical
  haveI : Nonempty (Fin L) := ⟨⟨0, hM.hL⟩⟩
  set m : ℝ := ⨅ l : Fin L, (sbar L M l.castSucc - v l) with hm
  set zb : ℝ := if v ∈ Vs L M then min (sbar L M (Fin.last L)) m else 0 with hzb
  have hmle : ∀ l : Fin L, m ≤ sbar L M l.castSucc - v l := fun l =>
    ciInf_le (Set.finite_range _).bddBelow l
  have hzb0 : 0 ≤ zb := by
    rw [hzb]; split_ifs with hVs
    · refine le_min (sbar_nonneg M hM _) ?_
      exact le_ciInf (fun l => by have := hVs.2 l; linarith)
    · exact le_refl _
  have hbound : ∀ z₁ : ℝ, zb ≤ z₁ →
      (sbar L M (Fin.last L) ≤ z₁ ∨ ∃ l : Fin L, sbar L M l.castSucc ≤ v l + z₁) := by
    intro z₁ hz
    by_cases hVs : v ∈ Vs L M
    · rw [hzb, if_pos hVs] at hz
      rcases min_le_iff.mp hz with h | h
      · left; exact h
      · right
        obtain ⟨l, hl⟩ := exists_eq_ciInf_of_finite (f := fun l : Fin L => sbar L M l.castSucc - v l)
        refine ⟨l, ?_⟩
        have : sbar L M l.castSucc - v l ≤ z₁ := by rw [hl, ← hm]; linarith
        linarith
    · rw [hzb, if_neg hVs] at hz
      have : ¬ ∀ l : Fin L, v l ≤ sbar L M l.castSucc := fun h => hVs ⟨hv, h⟩
      push_neg at this
      obtain ⟨l, hl⟩ := this
      right; exact ⟨l, by linarith⟩
  have hmono : ∀ z₁ z₂ : ℝ, zb ≤ z₁ → z₁ ≤ z₂ → gB M k v z₁ ≤ gB M k v z₂ := by
    intro z₁ z₂ h1 h12
    have h0 : 0 ≤ z₁ := le_trans hzb0 h1
    unfold gB gstep
    exact add_le_add (hB z₁ z₂ h0 h12 (hbound z₁ h1))
      (mul_le_mul_of_nonneg_left (hC z₁ z₂ h0 h12) hM.hγ0.le)
  have hsub : Set.Icc 0 zb ⊆ Set.Ici (0 : ℝ) := Set.Icc_subset_Ici_self
  obtain ⟨z0, hz0, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr hzb0) (hA.mono hsub)
  set S : Set ℝ := Set.Icc 0 zb ∩ gB M k v ⁻¹' Set.Iic (gB M k v z0) with hS
  have hSc : IsClosed S := (hA.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨z0, hz0, show gB M k v z0 ≤ gB M k v z0 from le_refl _⟩
  have hSbdd : BddBelow S := ⟨0, fun z hz => hz.1.1⟩
  have hzs : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  have hglob : ∀ z' : ℝ, 0 ≤ z' → gB M k v (sInf S) ≤ gB M k v z' := by
    intro z' hz'
    have h1 : gB M k v (sInf S) ≤ gB M k v z0 := hzs.2
    by_cases hle : z' ≤ zb
    · exact le_trans h1 (hmin ⟨hz', hle⟩)
    · push_neg at hle
      exact le_trans h1 (le_trans (hmin ⟨hzb0, le_refl _⟩) (hmono zb z' (le_refl _) hle.le))
  refine ⟨sInf S, ⟨⟨hzs.1.1, hglob⟩, ?_⟩, ?_⟩
  · rintro z' ⟨hz'0, hz'min⟩
    by_cases hle : z' ≤ zb
    · exact csInf_le hSbdd ⟨⟨hz'0, hle⟩, hz'min z0 hz0.1⟩
    · push_neg at hle
      exact le_trans hzs.1.2 hle.le
  · have hle : sInf S ≤ zb := hzs.1.2
    have h0 : 0 ≤ sInf S := hzs.1.1
    refine ⟨fun hVs => ?_, fun hVs => ?_⟩
    · rw [hzb, if_neg hVs] at hle; linarith
    · rw [hzb, if_pos hVs] at hle
      refine ⟨le_trans hle (min_le_left _ _), fun l => ?_⟩
      have := le_trans hle (min_le_right _ _)
      have := hmle l
      linarith

/-- The parent, modulo the single open key lemma D (pipeline monotonicity of `fB M k`). -/
theorem corollary_9_of_D {L : ℕ} (M : Data) (hM : Assumptions L M) (k : ℕ)
    (hD : ∀ w w' : Fin L → ℝ, w ∈ ZipkinLostSales.LNatural.V L →
      w' - w ∈ ZipkinLostSales.LNatural.V L → fB M k w ≤ fB M k w')
    (v : Fin L → ℝ) (hv : v ∈ ZipkinLostSales.LNatural.V L) :
    ∃ z : ℝ, IsOptOrder M k v z ∧ InZ L M v z :=
  assembly M hM k v hv (childA_gB_continuousOn M hM k v hv)
    (fun z₁ z₂ h0 h12 hb => childB_q_mono_beyond M hM v hv z₁ z₂ h0 h12 hb)
    (fun z₁ z₂ h0 h12 => childC_of_D M hM k hD v hv z₁ z₂ h0 h12)


/-! S2 part 1: decision-free costs `c47H`, `c47Bdf` and the one-period step. -/

noncomputable def c47H {L : ℕ} (M : Data) (i : ℕ) (Y : Fin L → ℝ) : ℝ :=
  ∫ D, q0 M (onHand Y 0 D i) ∂(Measure.pi fun _ : Fin L => M.μ)

noncomputable def c47Bdf {L : ℕ} (M : Data) : ℕ → (Fin L → ℝ) → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun Y => q0 M (vext Y 0 - vext Y 1) + M.γ * ∫ d, c47Bdf M n (nextZ Y d 0) ∂M.μ

theorem c47i_q0b (M : Data) [IsProbabilityMeasure M.μ] (hint : Integrable id M.μ) (y : ℝ) :
    |q0 M y| ≤ |q0 M 0| + (|M.c - M.p| + |M.h + M.p|) * |y| := by
  have h1 := c47_q0_lip M hint y 0
  rw [sub_zero] at h1
  have h2 := abs_sub_abs_le_abs_sub (q0 M y) (q0 M 0)
  linarith

theorem c47i_nextZ_d {L : ℕ} (v : Fin L → ℝ) (d d' z : ℝ) :
    ‖nextZ v d z - nextZ v d' z‖ ≤ |d - d'| := by
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr (fun l => ?_)
  rw [Real.norm_eq_abs, Pi.sub_apply]
  simp only [nextZ]
  split_ifs
  · have h := abs_max_sub_max_le_abs (vext v 0 - vext v 1 - d) (vext v 0 - vext v 1 - d') 0
    rw [show vext v 0 - vext v 1 - d - (vext v 0 - vext v 1 - d') = d' - d by ring,
      abs_sub_comm d' d] at h
    calc _ = |max (vext v 0 - vext v 1 - d) 0 - max (vext v 0 - vext v 1 - d') 0| := by
          congr 1; ring
      _ ≤ _ := h
  · simp

theorem c47i_intF {L : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (hint : Integrable id μ)
    (F : (Fin L → ℝ) → ℝ) (C : ℝ) (hC : 0 ≤ C) (hF : ∀ w w', |F w - F w'| ≤ C * ‖w - w'‖)
    (X : Fin L → ℝ) (z : ℝ) : Integrable (fun d => F (nextZ X d z)) μ := by
  have hFc : Continuous F := (LipschitzWith.of_dist_le_mul (K := ⟨C, hC⟩) (fun a b => by
      rw [Real.dist_eq, dist_eq_norm]; exact hF a b)).continuous
  have hb : Integrable (fun d => |F (nextZ X 0 z)| + C * |d|) μ :=
    (integrable_const _).add (hint.abs.const_mul C)
  refine hb.mono' (hFc.comp (c47_nextZ_cont X z)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun d => ?_)
  rw [Real.norm_eq_abs]
  have h1 := hF (nextZ X d z) (nextZ X 0 z)
  have h2 := c47i_nextZ_d X d 0 z
  rw [sub_zero] at h2
  have h3 := abs_sub_abs_le_abs_sub (F (nextZ X d z)) (F (nextZ X 0 z))
  have h4 := mul_le_mul_of_nonneg_left h2 hC
  linarith

theorem c47i_H_lip {L : ℕ} (M : Data) [IsProbabilityMeasure M.μ] (hint : Integrable id M.μ)
    (i : ℕ) (Y Y' : Fin L → ℝ) :
    |c47H M i Y - c47H M i Y'|
      ≤ ((|M.c - M.p| + |M.h + M.p|) * (2 * ((i : ℝ) + 1))) * ‖Y - Y'‖ := by
  have hb := c47i_q0b M hint
  have hi1 := c47f_int_phi M.μ hint (q0 M) (c47_q0_cont M hint) _ _ (by positivity) hb Y 0 i
  have hi2 := c47f_int_phi M.μ hint (q0 M) (c47_q0_cont M hint) _ _ (by positivity) hb Y' 0 i
  unfold c47H
  rw [← integral_sub hi1 hi2]
  have h := norm_integral_le_of_norm_le_const (μ := Measure.pi fun _ : Fin L => M.μ)
    (C := (|M.c - M.p| + |M.h + M.p|) * (2 * ((i : ℝ) + 1)) * ‖Y - Y'‖)
    (f := fun D => q0 M (onHand Y 0 D i) - q0 M (onHand Y' 0 D i))
    (Filter.Eventually.of_forall (fun D => by
      rw [Real.norm_eq_abs]
      calc _ ≤ (|M.c - M.p| + |M.h + M.p|) * |onHand Y 0 D i - onHand Y' 0 D i| :=
            c47_q0_lip M hint _ _
        _ ≤ _ := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (c47_onHand_lip Y Y' 0 D i) (by positivity)))
  simpa [Real.norm_eq_abs] using h

theorem c47i_Hsucc {m : ℕ} (M : Data) [IsProbabilityMeasure M.μ] (hint : Integrable id M.μ)
    (j : ℕ) (hj : j ≤ m) (Y : Fin (m + 1) → ℝ) :
    c47H M (j + 1) Y = ∫ d, c47H M j (nextZ Y d 0) ∂M.μ := by
  unfold c47H
  exact c47f_core M.μ hint (q0 M) (c47_q0_cont M hint) _ _ (by positivity) (c47i_q0b M hint)
    Y 0 j hj

theorem c47i_q_eq {m : ℕ} (M : Data) [IsProbabilityMeasure M.μ] (hint : Integrable id M.μ)
    (X : Fin (m + 1) → ℝ) (z : ℝ) :
    q M X z = M.γ ^ (m + 1) * ∫ d, c47H M m (nextZ X d z) ∂M.μ := by
  unfold q c47H yPlusL
  rw [c47f_core M.μ hint (q0 M) (c47_q0_cont M hint) _ _ (by positivity) (c47i_q0b M hint)
    X z m le_rfl]

theorem c47i_H0 {L : ℕ} (M : Data) [IsProbabilityMeasure M.μ] (hL : 0 < L) (Y : Fin L → ℝ) :
    c47H M 0 Y = q0 M (vext Y 0 - vext Y 1) := by
  unfold c47H
  have h : ∀ D : Fin L → ℝ, onHand Y 0 D 0 = vext Y 0 - vext Y 1 := fun D => by
    simp [onHand, arrival, hL, xext]
  simp [h]

theorem c47i_onHand_congr {L : ℕ} (Y Y' : Fin L → ℝ) (D : Fin L → ℝ) :
    ∀ i, (∀ j, j ≤ i → arrival Y 0 j = arrival Y' 0 j) → onHand Y 0 D i = onHand Y' 0 D i := by
  intro i
  induction i with
  | zero => intro h; exact h 0 le_rfl
  | succ i ih =>
    intro h
    show max (onHand Y 0 D i - vext D i) 0 + arrival Y 0 (i + 1)
      = max (onHand Y' 0 D i - vext D i) 0 + arrival Y' 0 (i + 1)
    rw [ih (fun j hj => h j (by omega)), h (i + 1) le_rfl]

theorem c47i_arr_z {m : ℕ} (X : Fin (m + 1) → ℝ) (d z : ℝ) (j : ℕ) (hj : j < m) :
    arrival (nextZ X d z) 0 j = arrival (nextZ X d 0) 0 j := by
  simp only [arrival, show j < m + 1 by omega, if_true, xext]
  rw [c47f_vext_nextZ X d z j (by omega), c47f_vext_nextZ X d z (j + 1) (by omega),
    c47f_vext_nextZ X d 0 j (by omega), c47f_vext_nextZ X d 0 (j + 1) (by omega)]
  ring

theorem c47i_H_inv {m : ℕ} (M : Data) (X : Fin (m + 1) → ℝ) (d z : ℝ) (i : ℕ) (hi : i < m) :
    c47H M i (nextZ X d z) = c47H M i (nextZ X d 0) := by
  unfold c47H
  congr 1
  funext D
  rw [c47i_onHand_congr _ _ D i (fun j hj => c47i_arr_z X d z j (by omega))]

theorem c47i_Bdf_sum {m : ℕ} (M : Data) [IsProbabilityMeasure M.μ] (hint : Integrable id M.μ) :
    ∀ n, n ≤ m + 1 → ∀ Y : Fin (m + 1) → ℝ,
      c47Bdf M n Y = ∑ i ∈ Finset.range n, M.γ ^ i * c47H M i Y := by
  intro n
  induction n with
  | zero => intro _ Y; simp [c47Bdf]
  | succ n ih =>
    intro hn Y
    have e : c47Bdf M (n + 1) Y
        = q0 M (vext Y 0 - vext Y 1) + M.γ * ∫ d, c47Bdf M n (nextZ Y d 0) ∂M.μ := rfl
    rw [e, Finset.sum_range_succ', pow_zero, one_mul, c47i_H0 M (Nat.succ_pos m) Y]
    have h1 : ∀ d, c47Bdf M n (nextZ Y d 0)
        = ∑ i ∈ Finset.range n, M.γ ^ i * c47H M i (nextZ Y d 0) := fun d => ih (by omega) _
    simp_rw [h1]
    rw [integral_finset_sum _ (fun i _ =>
      (c47i_intF M.μ hint _ _ (by positivity) (c47i_H_lip M hint i) Y 0).const_mul _)]
    rw [Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [integral_const_mul, ← c47i_Hsucc M hint i (by simp at hi; omega) Y, pow_succ]; ring

/-- S2 step: `q(X,z) + Bdf_L X = q0(x0) + γ E Bdf_L(nextZ X d z)`. -/
theorem c47i_step {m : ℕ} (M : Data) [IsProbabilityMeasure M.μ] (hint : Integrable id M.μ)
    (X : Fin (m + 1) → ℝ) (z : ℝ) :
    q M X z + c47Bdf M (m + 1) X
      = q0 M (vext X 0 - vext X 1) + M.γ * ∫ d, c47Bdf M (m + 1) (nextZ X d z) ∂M.μ := by
  have hs := c47i_Bdf_sum M hint (m + 1) le_rfl
  have eL : c47Bdf M (m + 1) X = q0 M (vext X 0 - vext X 1)
      + M.γ * ∑ i ∈ Finset.range m, M.γ ^ i * c47H M (i + 1) X := by
    rw [hs X, Finset.sum_range_succ', pow_zero, one_mul, c47i_H0 M (Nat.succ_pos m) X,
      Finset.mul_sum, add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have eR : ∫ d, c47Bdf M (m + 1) (nextZ X d z) ∂M.μ
      = ∑ i ∈ Finset.range m, M.γ ^ i * c47H M (i + 1) X
        + M.γ ^ m * ∫ d, c47H M m (nextZ X d z) ∂M.μ := by
    simp_rw [hs]
    rw [integral_finset_sum _ (fun i _ =>
      (c47i_intF M.μ hint _ _ (by positivity) (c47i_H_lip M hint i) X z).const_mul _),
      Finset.sum_range_succ, integral_const_mul]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i < m := by simpa using hi
    rw [integral_const_mul, c47i_Hsucc M hint i hi'.le X]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun d => c47i_H_inv M X d z i hi')
  rw [eL, eR, c47i_q_eq M hint X z]; ring

/-! S2 part 2: the L♮-convex model `c47fb` (= LNatural.fbar with c' = 0) and the identity
`fB_k + Bdf_L = fbar'_{k+L} + cE[d] Σ_{i<k+L} γ^i`. -/

noncomputable def c47E (L m : ℕ) : Fin L → ℝ := fun i => if (i : ℕ) ≤ m then 1 else 0

noncomputable def c47fb {L : ℕ} (M : Data) : ℕ → (Fin L → ℝ) → ℝ :=
  ZipkinLostSales.LNatural.fbar 0 (M.hh + (1 - M.γ) * M.c) (M.p - M.c) M.γ M.μ

theorem c47j_fb_succ {L : ℕ} (M : Data) (n : ℕ) (Y : Fin L → ℝ) :
    c47fb M (n + 1) Y = ⨅ ζ : Set.Iic (0 : ℝ),
      (ZipkinLostSales.LNatural.qhat0 (M.hh + (1 - M.γ) * M.c) (M.p - M.c) M.μ (vext Y 0 - vext Y 1)
        + M.γ * ∫ d, c47fb M n (ZipkinLostSales.LNatural.next Y d ζ) ∂M.μ) := by
  have e : c47fb M (n + 1) Y = ⨅ ζ : Set.Iic (0 : ℝ), ZipkinLostSales.LNatural.gstep 0
      (M.hh + (1 - M.γ) * M.c) (M.p - M.c) M.γ M.μ (c47fb M n) Y ζ := rfl
  rw [e]
  refine iInf_congr (fun ζ => ?_)
  unfold ZipkinLostSales.LNatural.gstep
  ring

theorem c47j_inf_add {ι : Type*} [Nonempty ι] (f : ι → ℝ) (hf : BddBelow (Set.range f)) (a : ℝ) :
    ⨅ i, (a + f i) = a + ⨅ i, f i := by
  obtain ⟨b, hb⟩ := hf
  have hb' : ∀ i, b ≤ f i := fun i => hb ⟨i, rfl⟩
  have hbdd : BddBelow (Set.range fun i => a + f i) :=
    ⟨a + b, by rintro _ ⟨i, rfl⟩; linarith [hb' i]⟩
  apply le_antisymm
  · have : (⨅ i, (a + f i)) - a ≤ ⨅ i, f i :=
      le_ciInf (fun i => by linarith [ciInf_le hbdd i])
    linarith
  · exact le_ciInf (fun i => by linarith [ciInf_le (⟨b, hb⟩ : BddBelow (Set.range f)) i])

theorem c47j_reindex (Φ : ℝ → ℝ) :
    ⨅ ζ : Set.Iic (0 : ℝ), Φ (-(ζ : ℝ)) = ⨅ z : Set.Ici (0 : ℝ), Φ z := by
  have h : Set.range (fun ζ : Set.Iic (0 : ℝ) => Φ (-(ζ : ℝ)))
      = Set.range (fun z : Set.Ici (0 : ℝ) => Φ z) := by
    ext y
    constructor
    · rintro ⟨ζ, rfl⟩
      exact ⟨⟨-(ζ : ℝ), Set.mem_Ici.mpr (neg_nonneg.mpr (Set.mem_Iic.mp ζ.2))⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨⟨-(z : ℝ), Set.mem_Iic.mpr (neg_nonpos.mpr (Set.mem_Ici.mp z.2))⟩, by simp⟩
  show sInf (Set.range _) = sInf (Set.range _)
  rw [h]

theorem c47j_q0_qhat (M : Data) [IsProbabilityMeasure M.μ] (hint : Integrable id M.μ) (y : ℝ) :
    q0 M y = ZipkinLostSales.LNatural.qhat0 (M.hh + (1 - M.γ) * M.c) (M.p - M.c) M.μ y
      + M.c * ∫ d, d ∂M.μ := by
  have hA : Integrable (fun d => max (y - d) 0) M.μ := ((integrable_const y).sub hint).pos_part
  have hB' : Integrable (fun d => max (d - y) 0) M.μ := (hint.sub (integrable_const y)).pos_part
  have hB : ∫ d, max (d - y) 0 ∂M.μ = ∫ d, max (y - d) 0 ∂M.μ - y + ∫ d, d ∂M.μ := by
    have : (fun d => max (d - y) 0) = fun d => (max (y - d) 0 - y) + id d := by
      funext d; simp only [id]
      rcases le_total d y with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    have h1 : Integrable (fun d => max (y - d) 0 - y) M.μ := hA.sub (integrable_const y)
    rw [this, integral_add h1 hint, integral_sub hA (integrable_const y)]
    simp [id]
  have hq : ZipkinLostSales.LNatural.qhat0 (M.hh + (1 - M.γ) * M.c) (M.p - M.c) M.μ y
      = (M.hh + (1 - M.γ) * M.c) * ∫ d, max (y - d) 0 ∂M.μ
        + (M.p - M.c) * ∫ d, max (d - y) 0 ∂M.μ := by
    unfold ZipkinLostSales.LNatural.qhat0 ZipkinLostSales.LNatural.qhat
    have : (fun d => (M.hh + (1 - M.γ) * M.c) * max (y - d) 0 + (M.p - M.c) * max (-(y - d)) 0)
        = fun d => (M.hh + (1 - M.γ) * M.c) * max (y - d) 0 + (M.p - M.c) * max (d - y) 0 := by
      funext d; rw [neg_sub]
    rw [this, integral_add (hA.const_mul _) (hB'.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [hq]; unfold q0 Data.h; rw [hB]; ring

theorem c47j_qhat_nonneg {L : ℕ} (M : Data) (hM : Assumptions L M) (y : ℝ) :
    0 ≤ ZipkinLostSales.LNatural.qhat0 (M.hh + (1 - M.γ) * M.c) (M.p - M.c) M.μ y := by
  have h1 : 0 ≤ M.hh + (1 - M.γ) * M.c :=
    add_nonneg hM.hhh (mul_nonneg (by linarith [hM.hγ1]) hM.hc)
  have h2 : 0 ≤ M.p - M.c := by linarith [hM.hph]
  unfold ZipkinLostSales.LNatural.qhat0 ZipkinLostSales.LNatural.qhat
  exact integral_nonneg fun d =>
    add_nonneg (mul_nonneg h1 (le_max_right _ _)) (mul_nonneg h2 (le_max_right _ _))

theorem c47j_fb_nonneg {L : ℕ} (M : Data) (hM : Assumptions L M) :
    ∀ n (Y : Fin L → ℝ), 0 ≤ c47fb M n Y := by
  intro n
  induction n with
  | zero => intro Y; exact le_rfl
  | succ n ih =>
    intro Y
    rw [c47j_fb_succ]
    exact Real.iInf_nonneg (fun ζ => add_nonneg (c47j_qhat_nonneg M hM _)
      (mul_nonneg hM.hγ0.le (integral_nonneg fun d => ih _)))

theorem c47j_next {L : ℕ} (v : Fin L → ℝ) (d ζ : ℝ) :
    ZipkinLostSales.LNatural.next v d ζ = nextZ v d (-ζ) := by
  funext l
  simp only [ZipkinLostSales.LNatural.next, nextZ]
  ring

theorem c47j_vext_E {L : ℕ} (Y : Fin L → ℝ) (a : ℝ) (i : ℕ) (hi : i < L) (j : ℕ) :
    vext (fun l => Y l + a * c47E L i l) j = vext Y j + (if j ≤ i then a else 0) := by
  unfold vext c47E
  by_cases hj : j < L
  · by_cases hji : j ≤ i <;> simp [hj, hji]
  · have : ¬ j ≤ i := by omega
    simp [hj, this]

theorem c47j_next_E {L : ℕ} (Y : Fin L → ℝ) (a d ζ : ℝ) (i : ℕ) (h1 : 1 ≤ i) (hi : i < L) :
    ZipkinLostSales.LNatural.next (fun l => Y l + a * c47E L i l) d ζ
      = fun l => ZipkinLostSales.LNatural.next Y d ζ l + a * c47E L (i - 1) l := by
  funext l
  simp only [ZipkinLostSales.LNatural.next]
  rw [c47j_vext_E Y a i hi 0, c47j_vext_E Y a i hi 1, c47j_vext_E Y a i hi ((l : ℕ) + 1)]
  simp only [c47E]
  split_ifs <;> first | omega | ring

theorem c47j_fb_inv {L : ℕ} (M : Data) :
    ∀ n i (Y : Fin L → ℝ) (a : ℝ), n ≤ i → i < L →
      c47fb M n (fun l => Y l + a * c47E L i l) = c47fb M n Y := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro i Y a hn hi
    rw [c47j_fb_succ, c47j_fb_succ]
    refine iInf_congr (fun ζ => ?_)
    rw [c47j_vext_E Y a i hi 0, c47j_vext_E Y a i hi 1, if_pos (by omega), if_pos (by omega)]
    have h : ∀ d, c47fb M n (ZipkinLostSales.LNatural.next (fun l => Y l + a * c47E L i l) d ζ)
        = c47fb M n (ZipkinLostSales.LNatural.next Y d ζ) := fun d => by
      rw [c47j_next_E Y a d ζ i (by omega) hi]
      exact ih (i - 1) _ a (by omega) (by omega)
    simp_rw [h]
    ring

theorem c47j_fb_const {m : ℕ} (M : Data) (X : Fin (m + 1) → ℝ) (d ζ : ℝ) (n : ℕ) (hn : n ≤ m) :
    c47fb M n (ZipkinLostSales.LNatural.next X d ζ) = c47fb M n (nextZ X d 0) := by
  have e : ZipkinLostSales.LNatural.next X d ζ = fun l => nextZ X d 0 l + (-ζ) * c47E (m + 1) m l := by
    funext l
    have hl : (l : ℕ) ≤ m := Nat.lt_succ_iff.mp l.2
    simp only [ZipkinLostSales.LNatural.next, nextZ, c47E, hl, if_true]
    ring
  rw [e]
  exact c47j_fb_inv M n m _ _ hn (Nat.lt_succ_self m)

theorem c47j_Bdf_lip {m : ℕ} (M : Data) [IsProbabilityMeasure M.μ] (hint : Integrable id M.μ)
    (n : ℕ) (hn : n ≤ m + 1) :
    ∃ C, 0 ≤ C ∧ ∀ w w' : Fin (m + 1) → ℝ, |c47Bdf M n w - c47Bdf M n w'| ≤ C * ‖w - w'‖ := by
  refine ⟨∑ i ∈ Finset.range n, |M.γ| ^ i * ((|M.c - M.p| + |M.h + M.p|) * (2 * ((i : ℝ) + 1))),
    Finset.sum_nonneg (fun i _ => by positivity), fun w w' => ?_⟩
  rw [c47i_Bdf_sum M hint n hn w, c47i_Bdf_sum M hint n hn w', ← Finset.sum_sub_distrib,
    Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← mul_sub, abs_mul, abs_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left (c47i_H_lip M hint i w w') (by positivity)

theorem c47j_geom (γ : ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), γ ^ i = 1 + γ * ∑ i ∈ Finset.range N, γ ^ i := by
  rw [Finset.sum_range_succ', pow_zero, Finset.mul_sum, add_comm]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem c47j_base {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M) :
    ∀ n, n ≤ m + 1 → ∀ Y : Fin (m + 1) → ℝ,
      c47Bdf M n Y = c47fb M n Y + M.c * (∫ d, d ∂M.μ) * ∑ i ∈ Finset.range n, M.γ ^ i := by
  haveI := hM.prob
  have hint := hM.integrable
  intro n
  induction n with
  | zero => intro _ Y; simp [c47Bdf, c47fb, ZipkinLostSales.LNatural.fbar]
  | succ n ih =>
    intro hn Y
    haveI : Nonempty (Set.Iic (0 : ℝ)) := ⟨⟨0, Set.mem_Iic.mpr le_rfl⟩⟩
    have e : c47Bdf M (n + 1) Y
        = q0 M (vext Y 0 - vext Y 1) + M.γ * ∫ d, c47Bdf M n (nextZ Y d 0) ∂M.μ := rfl
    rw [e, c47j_fb_succ]
    have hconst : ∀ ζ : Set.Iic (0 : ℝ),
        ZipkinLostSales.LNatural.qhat0 (M.hh + (1 - M.γ) * M.c) (M.p - M.c) M.μ (vext Y 0 - vext Y 1)
          + M.γ * ∫ d, c47fb M n (ZipkinLostSales.LNatural.next Y d ζ) ∂M.μ
        = ZipkinLostSales.LNatural.qhat0 (M.hh + (1 - M.γ) * M.c) (M.p - M.c) M.μ (vext Y 0 - vext Y 1)
          + M.γ * ∫ d, c47fb M n (nextZ Y d 0) ∂M.μ := fun ζ => by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun d =>
        c47j_fb_const (m := m) M Y d ζ n (by omega))]
    rw [iInf_congr hconst, ciInf_const]
    obtain ⟨C, hC, hlip⟩ := c47j_Bdf_lip (m := m) M hint n (by omega)
    have hI := c47i_intF M.μ hint _ C hC hlip Y 0
    have h2 : ∀ d, c47fb M n (nextZ Y d 0)
        = c47Bdf M n (nextZ Y d 0) - M.c * (∫ d, d ∂M.μ) * ∑ i ∈ Finset.range n, M.γ ^ i :=
      fun d => by rw [ih (by omega)]; ring
    simp_rw [h2]
    have hk : ∫ _d, M.c * (∫ d, d ∂M.μ) * ∑ i ∈ Finset.range n, M.γ ^ i ∂M.μ
        = M.c * (∫ d, d ∂M.μ) * ∑ i ∈ Finset.range n, M.γ ^ i := by simp
    rw [integral_sub hI (integrable_const _), hk, c47j_q0_qhat M hint, c47j_geom]
    ring

/-- S2 IDENTITY: `fB_k + Bdf_L = fbar'_{k+L} + cE[d] Σ_{i<k+L} γ^i` (L = m+1). -/
theorem c47j_ident {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M) :
    ∀ k (X : Fin (m + 1) → ℝ), fB M k X + c47Bdf M (m + 1) X
      = c47fb M (k + (m + 1)) X + M.c * (∫ d, d ∂M.μ) * ∑ i ∈ Finset.range (k + (m + 1)), M.γ ^ i := by
  haveI := hM.prob
  have hint := hM.integrable
  haveI : Nonempty (Set.Iic (0 : ℝ)) := ⟨⟨0, Set.mem_Iic.mpr le_rfl⟩⟩
  haveI : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.mem_Ici.mpr le_rfl⟩⟩
  intro k
  induction k with
  | zero =>
    intro X
    rw [Nat.zero_add, c47j_base M hM (m + 1) le_rfl X]
    simp [fB]
  | succ k ih =>
    intro X
    obtain ⟨Cb, hCb, hlipb⟩ := c47j_Bdf_lip M hint (m + 1) le_rfl
    obtain ⟨Bf, Cf, _, hCf, _, hlipf⟩ := c47_fB_props M hM k
    have hI : ∀ z, Integrable (fun d => fB M k (nextZ X d z) + c47Bdf M (m + 1) (nextZ X d z)) M.μ :=
      fun z => (c47i_intF M.μ hint _ _ hCf hlipf X z).add (c47i_intF M.μ hint _ _ hCb hlipb X z)
    have hLHS : ∀ z : ℝ, gstep M (fB M k) X z = (q0 M (vext X 0 - vext X 1) - c47Bdf M (m + 1) X)
        + M.γ * ∫ d, (fB M k (nextZ X d z) + c47Bdf M (m + 1) (nextZ X d z)) ∂M.μ := fun z => by
      have hs := c47i_step M hint X z
      unfold gstep
      rw [integral_add (c47i_intF M.μ hint _ _ hCf hlipf X z) (c47i_intF M.μ hint _ _ hCb hlipb X z)]
      linarith
    have hRHS : ∀ ζ : ℝ,
        ZipkinLostSales.LNatural.qhat0 (M.hh + (1 - M.γ) * M.c) (M.p - M.c) M.μ (vext X 0 - vext X 1)
          + M.γ * ∫ d, c47fb M (k + (m + 1)) (ZipkinLostSales.LNatural.next X d ζ) ∂M.μ
        = (ZipkinLostSales.LNatural.qhat0 (M.hh + (1 - M.γ) * M.c) (M.p - M.c) M.μ (vext X 0 - vext X 1)
            - M.γ * (M.c * (∫ d, d ∂M.μ) * ∑ i ∈ Finset.range (k + (m + 1)), M.γ ^ i))
          + M.γ * ∫ d, (fB M k (nextZ X d (-ζ)) + c47Bdf M (m + 1) (nextZ X d (-ζ))) ∂M.μ :=
      fun ζ => by
      have h1 : ∀ d, c47fb M (k + (m + 1)) (ZipkinLostSales.LNatural.next X d ζ)
          = (fB M k (nextZ X d (-ζ)) + c47Bdf M (m + 1) (nextZ X d (-ζ)))
            - M.c * (∫ d, d ∂M.μ) * ∑ i ∈ Finset.range (k + (m + 1)), M.γ ^ i := fun d => by
        rw [c47j_next, ih]; ring
      simp_rw [h1]
      have hk : ∫ _d, M.c * (∫ d, d ∂M.μ) * ∑ i ∈ Finset.range (k + (m + 1)), M.γ ^ i ∂M.μ
          = M.c * (∫ d, d ∂M.μ) * ∑ i ∈ Finset.range (k + (m + 1)), M.γ ^ i := by simp
      rw [integral_sub (hI (-ζ)) (integrable_const _), hk]
      ring
    have hlow : ∀ z : ℝ, M.γ * (M.c * (∫ d, d ∂M.μ) * ∑ i ∈ Finset.range (k + (m + 1)), M.γ ^ i)
          - ZipkinLostSales.LNatural.qhat0 (M.hh + (1 - M.γ) * M.c) (M.p - M.c) M.μ
            (vext X 0 - vext X 1)
        ≤ M.γ * ∫ d, (fB M k (nextZ X d z) + c47Bdf M (m + 1) (nextZ X d z)) ∂M.μ := fun z => by
      have h0 : 0 ≤ ZipkinLostSales.LNatural.qhat0 (M.hh + (1 - M.γ) * M.c) (M.p - M.c) M.μ
            (vext X 0 - vext X 1)
          + M.γ * ∫ d, c47fb M (k + (m + 1)) (ZipkinLostSales.LNatural.next X d (-z)) ∂M.μ :=
        add_nonneg (c47j_qhat_nonneg M hM _)
          (mul_nonneg hM.hγ0.le (integral_nonneg fun d => c47j_fb_nonneg M hM _ _))
      rw [hRHS, neg_neg] at h0
      linarith
    have hbdd : BddBelow (Set.range fun z : Set.Ici (0 : ℝ) =>
        M.γ * ∫ d, (fB M k (nextZ X d z) + c47Bdf M (m + 1) (nextZ X d z)) ∂M.μ) :=
      ⟨_, by rintro _ ⟨z, rfl⟩; exact hlow z⟩
    have hbdd' : BddBelow (Set.range fun ζ : Set.Iic (0 : ℝ) =>
        M.γ * ∫ d, (fB M k (nextZ X d (-(ζ : ℝ))) + c47Bdf M (m + 1) (nextZ X d (-(ζ : ℝ)))) ∂M.μ) :=
      ⟨_, by rintro _ ⟨ζ, rfl⟩; exact hlow _⟩
    have eL : fB M (k + 1) X = ⨅ z : Set.Ici (0 : ℝ), gstep M (fB M k) X z := rfl
    rw [show k + 1 + (m + 1) = (k + (m + 1)) + 1 by omega, eL, c47j_fb_succ,
      iInf_congr (fun z : Set.Ici (0 : ℝ) => hLHS z), iInf_congr (fun ζ : Set.Iic (0 : ℝ) => hRHS ζ),
      c47j_inf_add _ hbdd, c47j_inf_add _ hbdd',
      c47j_reindex (fun z => M.γ * ∫ d, (fB M k (nextZ X d z) + c47Bdf M (m + 1) (nextZ X d z)) ∂M.μ),
      c47j_q0_qhat M hint, c47j_geom]
    ring

/-! S3a: invariance of Bdf, Lipschitz of fb, the W-recursion
`fb_{a+1} - Bdf_{b+1} = -cE[d] + inf_{z>=0} γ E (fb_a - Bdf_b)(nextZ X d z)` for `b ≤ m`. -/

theorem c47k_nextZ_E {L : ℕ} (Y : Fin L → ℝ) (a d z : ℝ) (i : ℕ) (h1 : 1 ≤ i) (hi : i < L) :
    nextZ (fun l => Y l + a * c47E L i l) d z
      = fun l => nextZ Y d z l + a * c47E L (i - 1) l := by
  funext l
  simp only [nextZ]
  rw [c47j_vext_E Y a i hi 0, c47j_vext_E Y a i hi 1, c47j_vext_E Y a i hi ((l : ℕ) + 1)]
  simp only [c47E]
  split_ifs <;> first | omega | ring

theorem c47k_Bdf_inv {L : ℕ} (M : Data) :
    ∀ n i (Y : Fin L → ℝ) (a : ℝ), n ≤ i → i < L →
      c47Bdf M n (fun l => Y l + a * c47E L i l) = c47Bdf M n Y := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro i Y a hn hi
    show q0 M (vext (fun l => Y l + a * c47E L i l) 0 - vext (fun l => Y l + a * c47E L i l) 1)
        + M.γ * ∫ d, c47Bdf M n (nextZ (fun l => Y l + a * c47E L i l) d 0) ∂M.μ
      = q0 M (vext Y 0 - vext Y 1) + M.γ * ∫ d, c47Bdf M n (nextZ Y d 0) ∂M.μ
    rw [c47j_vext_E Y a i hi 0, c47j_vext_E Y a i hi 1, if_pos (by omega), if_pos (by omega)]
    have h : ∀ d, c47Bdf M n (nextZ (fun l => Y l + a * c47E L i l) d 0)
        = c47Bdf M n (nextZ Y d 0) := fun d => by
      rw [c47k_nextZ_E Y a d 0 i (by omega) hi]
      exact ih (i - 1) _ a (by omega) (by omega)
    simp_rw [h]
    ring

theorem c47k_Bdf_z {m : ℕ} (M : Data) (X : Fin (m + 1) → ℝ) (d z : ℝ) (b : ℕ) (hb : b ≤ m) :
    c47Bdf M b (nextZ X d z) = c47Bdf M b (nextZ X d 0) := by
  have e : nextZ X d z = fun l => nextZ X d 0 l + z * c47E (m + 1) m l := by
    funext l
    have hl : (l : ℕ) ≤ m := Nat.lt_succ_iff.mp l.2
    simp only [nextZ, c47E, hl, if_true]
    ring
  rw [e]
  exact c47k_Bdf_inv M b m _ _ hb (Nat.lt_succ_self m)

theorem c47k_fb_lip {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M) (a : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ w w' : Fin (m + 1) → ℝ, |c47fb M a w - c47fb M a w'| ≤ C * ‖w - w'‖ := by
  haveI := hM.prob
  have hint := hM.integrable
  by_cases ha : a ≤ m + 1
  · obtain ⟨C, hC, hl⟩ := c47j_Bdf_lip (m := m) M hint a ha
    refine ⟨C, hC, fun w w' => ?_⟩
    have e1 := c47j_base M hM a ha w
    have e2 := c47j_base M hM a ha w'
    have : c47fb M a w - c47fb M a w' = c47Bdf M a w - c47Bdf M a w' := by linarith
    rw [this]; exact hl w w'
  · obtain ⟨k, rfl⟩ : ∃ k, a = k + (m + 1) := ⟨a - (m + 1), by omega⟩
    obtain ⟨C, hC, hl⟩ := c47j_Bdf_lip (m := m) M hint (m + 1) le_rfl
    obtain ⟨_, Cf, _, hCf, _, hlf⟩ := c47_fB_props M hM k
    refine ⟨Cf + C, by positivity, fun w w' => ?_⟩
    have e1 := c47j_ident M hM k w
    have e2 := c47j_ident M hM k w'
    have : c47fb M (k + (m + 1)) w - c47fb M (k + (m + 1)) w'
        = (fB M k w - fB M k w') + (c47Bdf M (m + 1) w - c47Bdf M (m + 1) w') := by linarith
    rw [this]
    calc _ ≤ |fB M k w - fB M k w'| + |c47Bdf M (m + 1) w - c47Bdf M (m + 1) w'| := abs_add_le _ _
      _ ≤ Cf * ‖w - w'‖ + C * ‖w - w'‖ := add_le_add (hlf w w') (hl w w')
      _ = _ := by ring

/-- S3a: the W-recursion. -/
theorem c47k_Wrec {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M) (a b : ℕ) (hb : b ≤ m)
    (X : Fin (m + 1) → ℝ) :
    c47fb M (a + 1) X - c47Bdf M (b + 1) X
      = -(M.c * ∫ d, d ∂M.μ) + ⨅ z : Set.Ici (0 : ℝ),
          M.γ * ∫ d, (c47fb M a (nextZ X d z) - c47Bdf M b (nextZ X d z)) ∂M.μ := by
  haveI := hM.prob
  have hint := hM.integrable
  haveI : Nonempty (Set.Iic (0 : ℝ)) := ⟨⟨0, Set.mem_Iic.mpr le_rfl⟩⟩
  haveI : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.mem_Ici.mpr le_rfl⟩⟩
  obtain ⟨Cf, hCf, hlf⟩ := c47k_fb_lip M hM a
  obtain ⟨Cb, hCb, hlb⟩ := c47j_Bdf_lip (m := m) M hint b (by omega)
  have eB : c47Bdf M (b + 1) X
      = q0 M (vext X 0 - vext X 1) + M.γ * ∫ d, c47Bdf M b (nextZ X d 0) ∂M.μ := rfl
  have hz : ∀ z : ℝ, M.γ * ∫ d, (c47fb M a (nextZ X d z) - c47Bdf M b (nextZ X d z)) ∂M.μ
      = M.γ * ∫ d, c47fb M a (nextZ X d z) ∂M.μ - M.γ * ∫ d, c47Bdf M b (nextZ X d 0) ∂M.μ := by
    intro z
    rw [integral_sub (c47i_intF M.μ hint _ _ hCf hlf X z) (c47i_intF M.μ hint _ _ hCb hlb X z),
      mul_sub]
    congr 2
    exact integral_congr_ae (Filter.Eventually.of_forall fun d => c47k_Bdf_z M X d z b hb)
  have hnn : ∀ z : ℝ, 0 ≤ M.γ * ∫ d, c47fb M a (nextZ X d z) ∂M.μ := fun z =>
    mul_nonneg hM.hγ0.le (integral_nonneg fun d => c47j_fb_nonneg M hM _ _)
  have hbdd : BddBelow (Set.range fun ζ : Set.Iic (0 : ℝ) =>
      M.γ * ∫ d, c47fb M a (nextZ X d (-(ζ : ℝ))) ∂M.μ) :=
    ⟨0, by rintro _ ⟨ζ, rfl⟩; exact hnn _⟩
  have hbdd2 : BddBelow (Set.range fun z : Set.Ici (0 : ℝ) =>
      M.γ * ∫ d, c47fb M a (nextZ X d z) ∂M.μ) :=
    ⟨0, by rintro _ ⟨ζ, rfl⟩; exact hnn _⟩
  rw [c47j_fb_succ, eB]
  simp_rw [c47j_next]
  rw [c47j_inf_add _ hbdd, c47j_reindex (fun z => M.γ * ∫ d, c47fb M a (nextZ X d z) ∂M.μ),
    iInf_congr (fun z : Set.Ici (0 : ℝ) => hz z)]
  have e3 : ∀ z : Set.Ici (0 : ℝ), M.γ * ∫ d, c47fb M a (nextZ X d z) ∂M.μ
      - M.γ * ∫ d, c47Bdf M b (nextZ X d 0) ∂M.μ
      = -(M.γ * ∫ d, c47Bdf M b (nextZ X d 0) ∂M.μ) + M.γ * ∫ d, c47fb M a (nextZ X d z) ∂M.μ :=
    fun z => by ring
  rw [iInf_congr e3, c47j_inf_add _ hbdd2, c47j_q0_qhat M hint]
  ring

section c47lnat
open ZipkinLostSales.LNatural

/-! Generic consequences of `LNatConvexOn (V L) f` (Zipkin's L♮ on V × ℜ⁻) used by the
c47a69ec route (INDEX.md step 2): increments along the prefix direction `E_m` are nondecreasing
along any prefix direction `E_{m'}` with `m' ≤ m` (gives P1 for m' = m and P2 for m' = 0). -/


theorem c47E_anti (L m : ℕ) : Antitone (c47E L m) := by
  intro i j hij
  unfold c47E
  by_cases hj : (j : ℕ) ≤ m
  · have hi : (i : ℕ) ≤ m := le_trans (Fin.le_def.mp hij) hj
    simp [hi, hj]
  · by_cases hi : (i : ℕ) ≤ m <;> simp [hi, hj]

theorem c47E_nonneg (L m : ℕ) (i : Fin L) : 0 ≤ c47E L m i := by
  unfold c47E; split_ifs <;> norm_num

theorem c47l_memV {L : ℕ} (Y w : Fin L → ℝ) (hY : Y ∈ V L) (hw : Antitone w)
    (hw0 : ∀ i, 0 ≤ w i) : (fun i => Y i + w i) ∈ V L :=
  ⟨hY.1.add hw, fun i => add_nonneg (hY.2 i) (hw0 i)⟩

theorem c47l_smulE_anti (L m : ℕ) (a : ℝ) (ha : 0 ≤ a) : Antitone (fun i => a * c47E L m i) :=
  fun _ _ hij => mul_le_mul_of_nonneg_left (c47E_anti L m hij) ha

theorem c47l_lift {L : ℕ} {f : (Fin L → ℝ) → ℝ} (hf : LNatConvexOn (V L) f)
    (a b : Fin L → ℝ) (ξ η : ℝ) (hξ : ξ ≤ 0) (hη : η ≤ 0) (ha : a ∈ V L)
    (ha' : (fun i => a i - ξ) ∈ V L) (hb : b ∈ V L) (hb' : (fun i => b i - η) ∈ V L) :
    f (fun i => max (a i) (b i) - max ξ η) + f (fun i => min (a i) (b i) - min ξ η) ≤
      f (fun i => a i - ξ) + f (fun i => b i - η) := by
  have h := hf (Fin.snoc (α := fun _ => ℝ) a ξ) ⟨by simp [hξ], by simpa using ha, by simpa using ha'⟩
    (Fin.snoc (α := fun _ => ℝ) b η) ⟨by simp [hη], by simpa using hb, by simpa using hb'⟩
  have hsup : (Fin.snoc (α := fun _ => ℝ) a ξ ⊔ Fin.snoc (α := fun _ => ℝ) b η) =
      Fin.snoc (α := fun _ => ℝ) (a ⊔ b) (max ξ η) := by
    funext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  have hinf : (Fin.snoc (α := fun _ => ℝ) a ξ ⊓ Fin.snoc (α := fun _ => ℝ) b η) =
      Fin.snoc (α := fun _ => ℝ) (a ⊓ b) (min ξ η) := by
    funext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [hsup, hinf] at h
  simpa using h

/-- translation increments are monotone: `Z ≤ Z'` ⇒ `f(Z'+s) - f Z' ≥ f(Z+s) - f Z`. -/
theorem c47l_T {L : ℕ} {f : (Fin L → ℝ) → ℝ} (hf : LNatConvexOn (V L) f)
    (Z Z' : Fin L → ℝ) (hZZ : ∀ i, Z i ≤ Z' i) (s : ℝ) (hs : 0 ≤ s)
    (hZ : Z ∈ V L) (hZ' : Z' ∈ V L) (hZs' : (fun i => Z' i + s) ∈ V L) :
    f Z' + f (fun i => Z i + s) ≤ f (fun i => Z' i + s) + f Z := by
  have h := c47l_lift hf Z' Z (-s) 0 (by linarith) le_rfl hZ'
    (by simpa [sub_neg_eq_add] using hZs') hZ (by simpa using hZ)
  have e1 : (fun i => max (Z' i) (Z i) - max (-s) 0) = Z' := by
    funext i; rw [max_eq_left (hZZ i), max_eq_right (by linarith)]; ring
  have e2 : (fun i => min (Z' i) (Z i) - min (-s) 0) = fun i => Z i + s := by
    funext i; rw [min_eq_right (hZZ i), min_eq_left (by linarith)]; ring
  have e3 : (fun i => Z' i - -s) = fun i => Z' i + s := by funext i; ring
  have e4 : (fun i => Z i - 0) = Z := by funext i; ring
  rw [e1, e2, e3, e4] at h; exact h

/-- coordinatewise submodularity on `V`. -/
theorem c47l_S {L : ℕ} {f : (Fin L → ℝ) → ℝ} (hf : LNatConvexOn (V L) f)
    (x y : Fin L → ℝ) (hx : x ∈ V L) (hy : y ∈ V L) :
    f (fun i => max (x i) (y i)) + f (fun i => min (x i) (y i)) ≤ f x + f y := by
  have h := c47l_lift hf x y 0 0 le_rfl le_rfl hx (by simpa using hx) hy (by simpa using hy)
  simpa using h

/-- Main generic lemma: for `m' ≤ m`, `δ, s ≥ 0`, `Y ∈ V`:
`f(Y + sE_m) + f(Y + δE_{m'}) ≤ f(Y + δE_{m'} + sE_m) + f Y`. -/
theorem c47l_incr {L : ℕ} {f : (Fin L → ℝ) → ℝ} (hf : LNatConvexOn (V L) f)
    (m m' : ℕ) (hmm : m' ≤ m) (Y : Fin L → ℝ) (hY : Y ∈ V L) (δ s : ℝ) (hδ : 0 ≤ δ)
    (hs : 0 ≤ s) :
    f (fun i => Y i + s * c47E L m i) + f (fun i => Y i + δ * c47E L m' i) ≤
      f (fun i => Y i + δ * c47E L m' i + s * c47E L m i) + f Y := by
  have hY1 : (fun i => Y i + δ * c47E L m' i) ∈ V L :=
    c47l_memV Y _ hY (c47l_smulE_anti L m' δ hδ)
      (fun i => mul_nonneg hδ (c47E_nonneg L m' i))
  have hconst : Antitone (fun _ : Fin L => s) := fun _ _ _ => le_rfl
  have hY1s : (fun i => Y i + δ * c47E L m' i + s) ∈ V L :=
    c47l_memV _ (fun _ => s) hY1 hconst (fun _ => hs)
  have hYs : (fun i => Y i + s) ∈ V L := c47l_memV Y (fun _ => s) hY hconst (fun _ => hs)
  have hx : (fun i => Y i + δ * c47E L m' i + s * c47E L m i) ∈ V L :=
    c47l_memV _ _ hY1 (c47l_smulE_anti L m s hs) (fun i => mul_nonneg hs (c47E_nonneg L m i))
  have hT := c47l_T hf Y (fun i => Y i + δ * c47E L m' i)
    (fun i => le_add_of_nonneg_right (mul_nonneg hδ (c47E_nonneg L m' i))) s hs hY hY1 hY1s
  have hS := c47l_S hf (fun i => Y i + δ * c47E L m' i + s * c47E L m i)
    (fun i => Y i + s) hx hYs
  have e1 : (fun i => max (Y i + δ * c47E L m' i + s * c47E L m i) (Y i + s)) =
      fun i => Y i + δ * c47E L m' i + s := by
    funext i; unfold c47E
    by_cases h1 : (i : ℕ) ≤ m'
    · have h2 : (i : ℕ) ≤ m := le_trans h1 hmm
      simp only [h1, h2, if_true, mul_one]; rw [max_eq_left (by linarith)]
    · by_cases h2 : (i : ℕ) ≤ m
      · simp only [h1, h2, if_true, if_false, mul_one, mul_zero, add_zero]; exact max_self _
      · simp only [h1, h2, if_false, mul_zero, add_zero]; rw [max_eq_right (by linarith)]
  have e2 : (fun i => min (Y i + δ * c47E L m' i + s * c47E L m i) (Y i + s)) =
      fun i => Y i + s * c47E L m i := by
    funext i; unfold c47E
    by_cases h1 : (i : ℕ) ≤ m'
    · have h2 : (i : ℕ) ≤ m := le_trans h1 hmm
      simp only [h1, h2, if_true, mul_one]; rw [min_eq_right (by linarith)]
    · by_cases h2 : (i : ℕ) ≤ m
      · simp only [h1, h2, if_true, if_false, mul_one, mul_zero, add_zero]; exact min_self _
      · simp only [h1, h2, if_false, mul_zero, add_zero]; rw [min_eq_left (by linarith)]
  rw [e1, e2] at hS
  linarith

end c47lnat


/-! c47a69ec library (INDEX.md step 4): (a) continuous + midpoint convex on `[a,b]` ⇒ convex
(max principle); (b) the Chebyshev step of the Q-chain:
`∫ ψ d (∫ m) dμ ≤ ∫ ψ d (m d) dμ` when `ψ d` is convex on `[0,t]`, the increments of `ψ` in the
second variable are nonincreasing in `d`, and `m` is antitone with values in `[0,t]`.
Proof: Jensen in the second variable, then a rearrangement over `μ ⊗ μ`. -/

open MeasureTheory Set


theorem c47l_chord {φ : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn φ (Icc a b))
    (hmid : ∀ x h, 0 ≤ h → a ≤ x - h → x + h ≤ b → 2 * φ x ≤ φ (x - h) + φ (x + h))
    (x y : ℝ) (hax : a ≤ x) (hxy : x < y) (hyb : y ≤ b) (u : ℝ) (hu : u ∈ Icc x y) :
    φ u ≤ φ x + (φ y - φ x) * (u - x) / (y - x) := by
  have hyx : 0 < y - x := sub_pos.mpr hxy
  let g : ℝ → ℝ := fun u => φ u - (φ x + (φ y - φ x) * (u - x) / (y - x))
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hax hyb
  have hgc : ContinuousOn g (Icc x y) := by
    apply ContinuousOn.sub (hc.mono hsub)
    exact continuousOn_const.add
      ((continuousOn_const.mul (continuousOn_id.sub continuousOn_const)).div_const _)
  have hgx : g x = 0 := by simp [g]
  have hgy : g y = 0 := by
    simp only [g]; field_simp; ring
  obtain ⟨u0, hu0, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hxy.le) hgc
  have hmax' : ∀ v ∈ Icc x y, g v ≤ g u0 := fun v hv => isMaxOn_iff.mp hmax v hv
  by_contra hcon
  have hgu : 0 < g u := by simp only [g]; linarith [not_le.mp hcon]
  have hM : 0 < g u0 := lt_of_lt_of_le hgu (hmax' u hu)
  let K := Icc x y ∩ g ⁻¹' Ici (g u0)
  have hKc : IsClosed K := hgc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hKne : K.Nonempty := ⟨u0, hu0, show g u0 ≤ g u0 from le_refl _⟩
  have hKb : BddBelow K := ⟨x, fun w hw => hw.1.1⟩
  have hwK : sInf K ∈ K := hKc.csInf_mem hKne hKb
  set w := sInf K with hw
  have hw1 : w ∈ Icc x y := hwK.1
  have hw2 : g u0 ≤ g w := hwK.2
  have hwx : x < w := by
    rcases eq_or_lt_of_le hw1.1 with h | h
    · rw [← h] at hw2; linarith
    · exact h
  have hwy : w < y := by
    rcases eq_or_lt_of_le hw1.2 with h | h
    · rw [h] at hw2; linarith
    · exact h
  set h := min (w - x) (y - w) with hh
  have hpos : 0 < h := lt_min (by linarith) (by linarith)
  have h1 : h ≤ w - x := min_le_left _ _
  have h2 : h ≤ y - w := min_le_right _ _
  have hm := hmid w h hpos.le (by linarith) (by linarith)
  have haff : g (w - h) + g (w + h) - 2 * g w = φ (w - h) + φ (w + h) - 2 * φ w := by
    simp only [g]; field_simp; ring
  have hup : g (w + h) ≤ g u0 := hmax' _ ⟨by linarith, by linarith⟩
  have hlow : g (w - h) < g u0 := by
    by_contra hc2
    have hmem : w - h ∈ K := ⟨⟨by linarith, by linarith⟩, show g u0 ≤ g (w - h) from not_lt.mp hc2⟩
    have := csInf_le hKb hmem
    linarith
  linarith

theorem c47l_convex_of_mid {φ : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn φ (Icc a b))
    (hmid : ∀ x h, 0 ≤ h → a ≤ x - h → x + h ≤ b → 2 * φ x ≤ φ (x - h) + φ (x + h)) :
    ConvexOn ℝ (Icc a b) φ := by
  refine ⟨convex_Icc a b, ?_⟩
  intro x hx y hy α β hα hβ hαβ
  simp only [smul_eq_mul]
  have hα' : α = 1 - β := by linarith
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have hu : α * x + β * y ∈ Icc x y := ⟨by rw [hα']; nlinarith, by rw [hα']; nlinarith⟩
    have := c47l_chord hc hmid x y hx.1 hxy hy.2 _ hu
    have e : (φ y - φ x) * (α * x + β * y - x) / (y - x) = β * (φ y - φ x) := by
      rw [show α * x + β * y - x = β * (y - x) by rw [hα']; ring]
      have : y - x ≠ 0 := by linarith
      field_simp
    rw [e] at this
    have h2 : α * φ x + β * φ y = φ x + β * (φ y - φ x) := by rw [hα']; ring
    linarith
  · rw [← add_mul, hαβ, one_mul, ← add_mul, hαβ, one_mul]
  · have hu : α * x + β * y ∈ Icc y x := ⟨by rw [hα']; nlinarith, by rw [hα']; nlinarith⟩
    have := c47l_chord hc hmid y x hy.1 hxy hx.2 _ hu
    have e : (φ x - φ y) * (α * x + β * y - y) / (x - y) = α * (φ x - φ y) := by
      rw [show α * x + β * y - y = α * (x - y) by rw [hα']; ring]
      have : x - y ≠ 0 := by linarith
      field_simp
    rw [e] at this
    have h2 : α * φ x + β * φ y = φ y + α * (φ x - φ y) := by rw [hα']; ring
    linarith

theorem c47l_chebstep (μ : Measure ℝ) [IsProbabilityMeasure μ] (hint : Integrable id μ)
    (ψ : ℝ → ℝ → ℝ) (m : ℝ → ℝ) (t : ℝ)
    (hψc : Continuous (Function.uncurry ψ))
    (hconv : ∀ d, ConvexOn ℝ (Icc 0 t) (ψ d))
    (hsub : ∀ d d' a a', d ≤ d' → a ≤ a' → a ∈ Icc 0 t → a' ∈ Icc 0 t →
      ψ d' a' - ψ d' a ≤ ψ d a' - ψ d a)
    (hm : Antitone m) (hmt : ∀ d, m d ∈ Icc 0 t)
    (K : ℝ) (hbd : ∀ d a, a ∈ Icc 0 t → |ψ d a| ≤ K * (1 + |d|)) :
    ∫ d, ψ d (∫ d', m d' ∂μ) ∂μ ≤ ∫ d, ψ d (m d) ∂μ := by
  have hmm : Measurable m := hm.measurable
  have hmi : Integrable m μ := by
    refine (integrable_const t).mono' hmm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hmt d).1]; exact (hmt d).2
  have hmbar : (∫ d', m d' ∂μ) ∈ Icc 0 t := by
    refine ⟨integral_nonneg fun d => (hmt d).1, ?_⟩
    have := integral_mono hmi (integrable_const t) (fun d => (hmt d).2)
    simpa using this
  have hψa : ∀ d, Continuous (ψ d) := fun d =>
    hψc.comp (continuous_const.prodMk continuous_id)
  have hψd : ∀ a, Continuous (fun d => ψ d a) := fun a =>
    hψc.comp (continuous_id.prodMk continuous_const)
  have hK : Integrable (fun d : ℝ => K * (1 + |d|)) μ := by
    have : Integrable (fun d : ℝ => K + K * |d|) μ :=
      (integrable_const K).add (hint.abs.const_mul K)
    refine this.congr (Filter.Eventually.of_forall fun d => ?_); simp only; ring
  -- Jensen in the second variable
  have hJ : ∀ d, ψ d (∫ d', m d' ∂μ) ≤ ∫ d', ψ d (m d') ∂μ := by
    intro d
    refine (hconv d).map_integral_le ((hψa d).continuousOn) isClosed_Icc
      (Filter.Eventually.of_forall hmt) hmi ?_
    refine (integrable_const (K * (1 + |d|))).mono'
      ((hψa d).measurable.comp hmm).aestronglyMeasurable (Filter.Eventually.of_forall fun d' => ?_)
    rw [Real.norm_eq_abs]; exact hbd d _ (hmt d')
  -- the product function
  let P : ℝ × ℝ → ℝ := fun p => ψ p.1 (m p.2)
  have hPm : Measurable P := hψc.measurable.comp (measurable_fst.prodMk (hmm.comp measurable_snd))
  have hPi : Integrable P (μ.prod μ) := by
    refine (hK.comp_fst μ).mono' hPm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]; exact hbd p.1 _ (hmt p.2)
  let Q : ℝ → ℝ := fun d => ψ d (m d)
  have hQm : Measurable Q := hψc.measurable.comp (measurable_id.prodMk hmm)
  have hQi : Integrable Q μ := by
    refine hK.mono' hQm.aestronglyMeasurable (Filter.Eventually.of_forall fun d => ?_)
    rw [Real.norm_eq_abs]; exact hbd d _ (hmt d)
  have hPs : Integrable (fun p : ℝ × ℝ => P p.swap) (μ.prod μ) := hPi.swap
  -- rearrangement
  have hpos : ∀ p : ℝ × ℝ, 0 ≤ Q p.1 + Q p.2 - P p - P p.swap := by
    intro p
    simp only [P, Q, Prod.fst_swap, Prod.snd_swap]
    rcases le_total p.1 p.2 with h | h
    · have := hsub p.1 p.2 (m p.2) (m p.1) h (hm h) (hmt _) (hmt _); linarith
    · have := hsub p.2 p.1 (m p.1) (m p.2) h (hm h) (hmt _) (hmt _); linarith
  have hint0 : 0 ≤ ∫ p, (Q p.1 + Q p.2 - P p - P p.swap) ∂(μ.prod μ) := integral_nonneg hpos
  have i1 : Integrable (fun p : ℝ × ℝ => Q p.1) (μ.prod μ) := hQi.comp_fst μ
  have i2 : Integrable (fun p : ℝ × ℝ => Q p.2) (μ.prod μ) := hQi.comp_snd μ
  rw [integral_sub (f := fun p : ℝ × ℝ => Q p.1 + Q p.2 - P p) (g := fun p => P p.swap)
      ((i1.add i2).sub hPi) hPs,
    integral_sub (f := fun p : ℝ × ℝ => Q p.1 + Q p.2) (g := P) (i1.add i2) hPi,
    integral_add (f := fun p : ℝ × ℝ => Q p.1) (g := fun p => Q p.2) i1 i2] at hint0
  have e1 : ∫ p, Q p.1 ∂(μ.prod μ) = ∫ d, Q d ∂μ := by
    rw [integral_fun_fst (μ := μ) (ν := μ) Q]; simp
  have e2 : ∫ p, Q p.2 ∂(μ.prod μ) = ∫ d, Q d ∂μ := by
    rw [integral_fun_snd (μ := μ) (ν := μ) Q]; simp
  have e3 : ∫ p, P p.swap ∂(μ.prod μ) = ∫ p, P p ∂(μ.prod μ) := integral_prod_swap P
  have e4 : ∫ p, P p ∂(μ.prod μ) = ∫ d, ∫ d', ψ d (m d') ∂μ ∂μ := integral_prod P hPi
  rw [e1, e2, e3, e4] at hint0
  have hJi : ∫ d, ψ d (∫ d', m d' ∂μ) ∂μ ≤ ∫ d, ∫ d', ψ d (m d') ∂μ ∂μ := by
    refine integral_mono ?_ hPi.integral_prod_left hJ
    refine hK.mono' (hψd _).measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun d => ?_)
    rw [Real.norm_eq_abs]; exact hbd d _ hmbar
  have : ∫ d, ∫ d', ψ d (m d') ∂μ ∂μ ≤ ∫ d, Q d ∂μ := by linarith
  exact le_trans hJi this

/-! S3b/S4 (session 10): `c47mr` (expected extra on-hand), the generic Chebyshev step for
`c47W = fb_{k+j} - Bdf_j`, the Q-chain and property A. -/

theorem c47m_nextZ_memV {L : ℕ} (v : Fin L → ℝ) (hv : v ∈ ZipkinLostSales.LNatural.V L) (d : ℝ)
    {z : ℝ} (hz : 0 ≤ z) : nextZ v d z ∈ ZipkinLostSales.LNatural.V L := by
  obtain ⟨hanti, hnn⟩ := hv
  have hvext_nn : ∀ l, 0 ≤ vext v l := fun l => by
    unfold vext; split_ifs
    · exact hnn _
    · exact le_refl 0
  have hvext_anti : ∀ a b : ℕ, a ≤ b → vext v b ≤ vext v a := by
    intro a b hab
    unfold vext
    split_ifs with h1 h2 h2
    · exact hanti (Fin.mk_le_mk.mpr hab)
    · omega
    · exact hnn _
    · exact le_refl 0
  refine ⟨fun a b hab => ?_, fun l => ?_⟩
  · simp only [nextZ]
    have := hvext_anti ((a : ℕ) + 1) ((b : ℕ) + 1) (by have : (a : ℕ) ≤ b := hab; omega)
    split_ifs with hb ha <;> first
      | linarith [this, le_max_right (vext v 0 - vext v 1 - d) 0]
      | (exfalso; have : (a : ℕ) ≤ b := hab; omega)
  · simp only [nextZ]
    split_ifs <;> linarith [le_max_right (vext v 0 - vext v 1 - d) 0, hvext_nn ((l : ℕ) + 1)]

noncomputable def c47eps {L : ℕ} (Y : Fin L → ℝ) (t d : ℝ) : ℝ :=
  max (vext Y 0 - vext Y 1 + t - d) 0 - max (vext Y 0 - vext Y 1 - d) 0

theorem c47m_e_mono {x x' t d d' : ℝ} (ht : 0 ≤ t) (h : x - d ≤ x' - d') :
    max (x + t - d) 0 - max (x - d) 0 ≤ max (x' + t - d') 0 - max (x' - d') 0 := by
  simp only [max_def]; split_ifs <;> linarith

theorem c47m_eps_mem {L : ℕ} (Y : Fin L → ℝ) {t : ℝ} (ht : 0 ≤ t) (d : ℝ) :
    c47eps Y t d ∈ Set.Icc 0 t := by
  unfold c47eps; simp only [max_def, Set.mem_Icc]; constructor <;> split_ifs <;> linarith

theorem c47m_eps_anti {L : ℕ} (Y : Fin L → ℝ) {t : ℝ} (ht : 0 ≤ t) : Antitone (c47eps Y t) :=
  fun d d' h => by unfold c47eps; exact c47m_e_mono ht (by linarith)

theorem c47m_x0_E0 {m : ℕ} (Y : Fin (m + 1) → ℝ) (δ : ℝ) :
    vext (fun l => Y l + δ * c47E (m + 1) 0 l) 0 - vext (fun l => Y l + δ * c47E (m + 1) 0 l) 1
      = vext Y 0 - vext Y 1 + δ := by
  rw [c47j_vext_E Y δ 0 (Nat.succ_pos m) 0, c47j_vext_E Y δ 0 (Nat.succ_pos m) 1]
  simp only [le_refl, if_true, show ¬ (1 : ℕ) ≤ 0 by omega, if_false]
  ring

theorem c47m_nextZ_E0 {m : ℕ} (Y : Fin (m + 1) → ℝ) (t d z : ℝ) :
    nextZ (fun l => Y l + t * c47E (m + 1) 0 l) d z
      = fun l => nextZ Y d z l + c47eps Y t d * c47E (m + 1) 0 l := by
  funext l
  have hx := c47m_x0_E0 Y t
  have hv : vext (fun l => Y l + t * c47E (m + 1) 0 l) ((l : ℕ) + 1) = vext Y ((l : ℕ) + 1) := by
    rw [c47j_vext_E Y t 0 (Nat.succ_pos m)]
    simp
  simp only [nextZ, c47eps]
  rw [hx, hv]
  simp only [c47E]
  split_ifs <;> first | omega | ring

theorem c47m_nextZ_d {m : ℕ} (Y : Fin (m + 1) → ℝ) (d d' z : ℝ) :
    nextZ Y d z = fun l => nextZ Y d' z l
      + (max (vext Y 0 - vext Y 1 - d) 0 - max (vext Y 0 - vext Y 1 - d') 0) * c47E (m + 1) 0 l := by
  funext l
  simp only [nextZ, c47E]
  split_ifs <;> first | omega | ring

theorem c47m_dd_nonneg (x d d' : ℝ) (h : d ≤ d') : 0 ≤ max (x - d) 0 - max (x - d') 0 := by
  have := max_le_max (show x - d' ≤ x - d by linarith) (le_refl (0 : ℝ))
  linarith

noncomputable def c47mr {L : ℕ} (M : Data) (t : ℝ) : ℕ → (Fin L → ℝ) → ℝ
  | 0 => fun Y => ∫ d, c47eps Y t d ∂M.μ
  | j + 1 => fun Y => ∫ d, c47mr M t j (nextZ Y d 0) ∂M.μ

theorem c47m_int_bdd (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ} (hf : Antitone f) {t : ℝ}
    (hb : ∀ d, f d ∈ Set.Icc 0 t) : Integrable f μ := by
  refine (integrable_const t).mono' hf.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun d => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hb d).1]; exact (hb d).2

theorem c47m_int_mem (μ : Measure ℝ) [IsProbabilityMeasure μ] {f : ℝ → ℝ} (hf : Antitone f)
    {t : ℝ} (hb : ∀ d, f d ∈ Set.Icc 0 t) : (∫ d, f d ∂μ) ∈ Set.Icc 0 t := by
  refine ⟨integral_nonneg fun d => (hb d).1, ?_⟩
  have := integral_mono (c47m_int_bdd μ hf hb) (integrable_const t) (fun d => (hb d).2)
  simpa using this

theorem c47m_mr_props {m : ℕ} (M : Data) [IsProbabilityMeasure M.μ] {t : ℝ} (ht : 0 ≤ t) :
    ∀ j (Y : Fin (m + 1) → ℝ), c47mr M t j Y ∈ Set.Icc 0 t ∧
      ∀ δ : ℝ, 0 ≤ δ → c47mr M t j Y ≤ c47mr M t j (fun l => Y l + δ * c47E (m + 1) 0 l) := by
  intro j
  induction j with
  | zero =>
    intro Y
    refine ⟨c47m_int_mem M.μ (c47m_eps_anti Y ht) (c47m_eps_mem Y ht), fun δ hδ => ?_⟩
    show ∫ d, c47eps Y t d ∂M.μ ≤ ∫ d, c47eps (fun l => Y l + δ * c47E (m + 1) 0 l) t d ∂M.μ
    refine integral_mono (c47m_int_bdd M.μ (c47m_eps_anti Y ht) (c47m_eps_mem Y ht))
      (c47m_int_bdd M.μ (c47m_eps_anti _ ht) (c47m_eps_mem _ ht)) (fun d => ?_)
    unfold c47eps
    rw [c47m_x0_E0 Y δ]
    exact c47m_e_mono ht (by linarith)
  | succ j ih =>
    have hanti : ∀ Y' : Fin (m + 1) → ℝ, Antitone (fun d => c47mr M t j (nextZ Y' d 0)) := by
      intro Y' d d' hdd
      show c47mr M t j (nextZ Y' d' 0) ≤ c47mr M t j (nextZ Y' d 0)
      rw [c47m_nextZ_d Y' d d' 0]
      exact (ih _).2 _ (c47m_dd_nonneg _ d d' hdd)
    intro Y
    refine ⟨c47m_int_mem M.μ (hanti Y) (fun d => (ih _).1), fun δ hδ => ?_⟩
    show ∫ d, c47mr M t j (nextZ Y d 0) ∂M.μ
      ≤ ∫ d, c47mr M t j (nextZ (fun l => Y l + δ * c47E (m + 1) 0 l) d 0) ∂M.μ
    refine integral_mono (c47m_int_bdd M.μ (hanti Y) (fun d => (ih _).1))
      (c47m_int_bdd M.μ (hanti _) (fun d => (ih _).1)) (fun d => ?_)
    show c47mr M t j (nextZ Y d 0) ≤ c47mr M t j (nextZ (fun l => Y l + δ * c47E (m + 1) 0 l) d 0)
    rw [c47m_nextZ_E0 Y δ d 0]
    exact (ih _).2 _ (c47m_eps_mem Y hδ d).1

theorem c47m_mr_inv {m : ℕ} (M : Data) (t : ℝ) :
    ∀ j i (Y : Fin (m + 1) → ℝ) (a : ℝ), j < i → i < m + 1 →
      c47mr M t j (fun l => Y l + a * c47E (m + 1) i l) = c47mr M t j Y := by
  intro j
  induction j with
  | zero =>
    intro i Y a hj hi
    show ∫ d, c47eps (fun l => Y l + a * c47E (m + 1) i l) t d ∂M.μ = ∫ d, c47eps Y t d ∂M.μ
    have h : ∀ d, c47eps (fun l => Y l + a * c47E (m + 1) i l) t d = c47eps Y t d := fun d => by
      unfold c47eps
      rw [c47j_vext_E Y a i hi 0, c47j_vext_E Y a i hi 1, if_pos (by omega), if_pos (by omega)]
      have e : vext Y 0 + a - (vext Y 1 + a) = vext Y 0 - vext Y 1 := by ring
      rw [e]
    simp_rw [h]
  | succ j ih =>
    intro i Y a hj hi
    show ∫ d, c47mr M t j (nextZ (fun l => Y l + a * c47E (m + 1) i l) d 0) ∂M.μ
      = ∫ d, c47mr M t j (nextZ Y d 0) ∂M.μ
    have h : ∀ d, c47mr M t j (nextZ (fun l => Y l + a * c47E (m + 1) i l) d 0)
        = c47mr M t j (nextZ Y d 0) := fun d => by
      rw [c47k_nextZ_E Y a d 0 i (by omega) hi]
      exact ih (i - 1) _ a (by omega) (by omega)
    simp_rw [h]

theorem c47m_mr_z {m : ℕ} (M : Data) (t : ℝ) (X : Fin (m + 1) → ℝ) (d z : ℝ) (j : ℕ)
    (hj : j < m) : c47mr M t j (nextZ X d z) = c47mr M t j (nextZ X d 0) := by
  have e : nextZ X d z = fun l => nextZ X d 0 l + z * c47E (m + 1) m l := by
    funext l
    have hl : (l : ℕ) ≤ m := Nat.lt_succ_iff.mp l.2
    simp only [nextZ, c47E, hl, if_true]
    ring
  rw [e]
  exact c47m_mr_inv M t j m _ _ hj (Nat.lt_succ_self m)

/-- `W^j = fb_{k+j} - Bdf_j`. -/
noncomputable def c47W {L : ℕ} (M : Data) (k j : ℕ) (X : Fin L → ℝ) : ℝ :=
  c47fb M (k + j) X - c47Bdf M j X

theorem c47m_W_lip {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M) (k j : ℕ) (hj : j ≤ m + 1) :
    ∃ C, 0 ≤ C ∧ ∀ w w' : Fin (m + 1) → ℝ, |c47W M k j w - c47W M k j w'| ≤ C * ‖w - w'‖ := by
  haveI := hM.prob
  obtain ⟨Cf, hCf, hlf⟩ := c47k_fb_lip M hM (k + j)
  obtain ⟨Cb, hCb, hlb⟩ := c47j_Bdf_lip (m := m) M hM.integrable j hj
  refine ⟨Cf + Cb, by positivity, fun w w' => ?_⟩
  have h1 := abs_le.mp (hlf w w')
  have h2 := abs_le.mp (hlb w w')
  unfold c47W
  rw [add_mul, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem c47m_Wrec {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M) (k j : ℕ) (hj : j ≤ m)
    (X : Fin (m + 1) → ℝ) :
    c47W M k (j + 1) X = -(M.c * ∫ d, d ∂M.μ) + ⨅ z : Set.Ici (0 : ℝ),
      M.γ * ∫ d, c47W M k j (nextZ X d z) ∂M.μ := by
  simp only [c47W]
  exact c47k_Wrec M hM (k + j) j hj X

theorem c47m_W_bdd {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M) (k j : ℕ) (hj : j ≤ m)
    (X : Fin (m + 1) → ℝ) :
    BddBelow (Set.range fun z : Set.Ici (0 : ℝ) => M.γ * ∫ d, c47W M k j (nextZ X d z) ∂M.μ) := by
  haveI := hM.prob
  have hint := hM.integrable
  obtain ⟨Cf, hCf, hlf⟩ := c47k_fb_lip M hM (k + j)
  obtain ⟨Cb, hCb, hlb⟩ := c47j_Bdf_lip (m := m) M hint j (by omega)
  refine ⟨-(M.γ * ∫ d, c47Bdf M j (nextZ X d 0) ∂M.μ), ?_⟩
  rintro _ ⟨z, rfl⟩
  simp only [c47W]
  rw [integral_sub (c47i_intF M.μ hint _ _ hCf hlf X (z : ℝ))
    (c47i_intF M.μ hint _ _ hCb hlb X (z : ℝ))]
  have e : ∫ d, c47Bdf M j (nextZ X d (z : ℝ)) ∂M.μ = ∫ d, c47Bdf M j (nextZ X d 0) ∂M.μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun d => c47k_Bdf_z M X d z j hj)
  rw [e, mul_sub]
  have h0 : 0 ≤ ∫ d, c47fb M (k + j) (nextZ X d (z : ℝ)) ∂M.μ :=
    integral_nonneg fun d => c47j_fb_nonneg M hM _ _
  have := mul_nonneg hM.hγ0.le h0
  linarith

theorem c47m_psi_cont {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M) (k j : ℕ) (hj : j ≤ m + 1)
    (i : ℕ) (Y : Fin (m + 1) → ℝ) (z : ℝ) :
    Continuous (fun p : ℝ × ℝ => c47W M k j (fun l => nextZ Y p.1 z l + p.2 * c47E (m + 1) i l)) := by
  obtain ⟨C, hC, hl⟩ := c47m_W_lip M hM k j hj
  have hWc : Continuous (c47W M k j : (Fin (m + 1) → ℝ) → ℝ) :=
    (LipschitzWith.of_dist_le_mul (K := ⟨C, hC⟩) (fun a b => by
      rw [Real.dist_eq, dist_eq_norm]; exact hl a b)).continuous
  refine hWc.comp (continuous_pi fun l => ?_)
  exact ((continuous_apply l).comp ((c47_nextZ_cont Y z).comp continuous_fst)).add
    (continuous_snd.mul continuous_const)

theorem c47m_psi_bd {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M) (k j : ℕ) (hj : j ≤ m + 1)
    (i : ℕ) (Y : Fin (m + 1) → ℝ) (z : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ K, ∀ d a, a ∈ Set.Icc 0 t →
      |c47W M k j (fun l => nextZ Y d z l + a * c47E (m + 1) i l)| ≤ K * (1 + |d|) := by
  obtain ⟨C, hC, hl⟩ := c47m_W_lip M hM k j hj
  refine ⟨|c47W M k j (nextZ Y 0 z)| + C * t + C, fun d a ha => ?_⟩
  have hn : ‖(fun l => nextZ Y d z l + a * c47E (m + 1) i l) - nextZ Y 0 z‖ ≤ |d| + t := by
    refine (pi_norm_le_iff_of_nonneg (add_nonneg (abs_nonneg d) ht)).mpr fun l => ?_
    have hd := (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mp (c47i_nextZ_d Y d 0 z) l
    rw [Real.norm_eq_abs, Pi.sub_apply, sub_zero] at hd
    rw [Real.norm_eq_abs]
    show |nextZ Y d z l + a * c47E (m + 1) i l - nextZ Y 0 z l| ≤ |d| + t
    have hE0 : 0 ≤ c47E (m + 1) i l := c47E_nonneg _ _ _
    have hE1 : c47E (m + 1) i l ≤ 1 := by unfold c47E; split_ifs <;> norm_num
    have h1 : 0 ≤ a * c47E (m + 1) i l := mul_nonneg ha.1 hE0
    have h2 : a * c47E (m + 1) i l ≤ t := (mul_le_of_le_one_right ha.1 hE1).trans ha.2
    rw [abs_le] at hd ⊢
    constructor <;> linarith [hd.1, hd.2]
  have h3 := hl (fun l => nextZ Y d z l + a * c47E (m + 1) i l) (nextZ Y 0 z)
  have h4 := mul_le_mul_of_nonneg_left hn hC
  have h5 := abs_sub_abs_le_abs_sub (c47W M k j (fun l => nextZ Y d z l + a * c47E (m + 1) i l))
    (c47W M k j (nextZ Y 0 z))
  nlinarith [abs_nonneg (c47W M k j (nextZ Y 0 z)), abs_nonneg d, mul_nonneg hC ht,
    mul_nonneg (mul_nonneg hC ht) (abs_nonneg d),
    mul_nonneg (abs_nonneg (c47W M k j (nextZ Y 0 z))) (abs_nonneg d)]

theorem c47m_psi_int {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M) (k j : ℕ) (hj : j ≤ m + 1)
    (i : ℕ) (Y : Fin (m + 1) → ℝ) (z : ℝ) {t : ℝ} (ht : 0 ≤ t) (g : ℝ → ℝ) (hg : Measurable g)
    (hgt : ∀ d, g d ∈ Set.Icc 0 t) :
    Integrable (fun d => c47W M k j (fun l => nextZ Y d z l + g d * c47E (m + 1) i l)) M.μ := by
  haveI := hM.prob
  obtain ⟨K, hK⟩ := c47m_psi_bd M hM k j hj i Y z ht
  have hgi : Integrable (fun d : ℝ => K * (1 + |d|)) M.μ :=
    ((integrable_const (1 : ℝ)).add hM.integrable.abs).const_mul K
  refine hgi.mono' ?_ (Filter.Eventually.of_forall fun d => ?_)
  · exact ((c47m_psi_cont M hM k j hj i Y z).measurable.comp
      (measurable_id.prodMk hg)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact hK d (g d) (hgt d)

theorem c47m_mid {L : ℕ} {f : (Fin L → ℝ) → ℝ}
    (hf : ZipkinLostSales.LNatural.LNatConvexOn (ZipkinLostSales.LNatural.V L) f) (j : ℕ)
    (Y : Fin L → ℝ) (hY : Y ∈ ZipkinLostSales.LNatural.V L) (x h : ℝ) (hh : 0 ≤ h)
    (hxh : 0 ≤ x - h) :
    2 * f (fun l => Y l + x * c47E L j l)
      ≤ f (fun l => Y l + (x - h) * c47E L j l) + f (fun l => Y l + (x + h) * c47E L j l) := by
  have hV : (fun l => Y l + (x - h) * c47E L j l) ∈ ZipkinLostSales.LNatural.V L :=
    c47l_memV Y _ hY (c47l_smulE_anti L j _ hxh) (fun i => mul_nonneg hxh (c47E_nonneg L j i))
  have H : f (fun i => Y i + (x - h) * c47E L j i + h * c47E L j i)
      + f (fun i => Y i + (x - h) * c47E L j i + h * c47E L j i)
      ≤ f (fun i => Y i + (x - h) * c47E L j i + h * c47E L j i + h * c47E L j i)
        + f (fun i => Y i + (x - h) * c47E L j i) :=
    c47l_incr hf j j le_rfl _ hV h h hh hh
  have e1 : (fun i => Y i + (x - h) * c47E L j i + h * c47E L j i)
      = fun l => Y l + x * c47E L j l := by funext i; ring
  have e2 : (fun i => Y i + (x - h) * c47E L j i + h * c47E L j i + h * c47E L j i)
      = fun l => Y l + (x + h) * c47E L j l := by funext i; ring
  rw [e2, e1] at H
  linarith

theorem c47m_sub {L : ℕ} {f : (Fin L → ℝ) → ℝ}
    (hf : ZipkinLostSales.LNatural.LNatConvexOn (ZipkinLostSales.LNatural.V L) f) (j : ℕ)
    (Y : Fin L → ℝ) (hY : Y ∈ ZipkinLostSales.LNatural.V L) (δ a a' : ℝ) (hδ : 0 ≤ δ)
    (ha : 0 ≤ a) (haa : a ≤ a') :
    f (fun l => Y l + a' * c47E L j l) - f (fun l => Y l + a * c47E L j l)
      ≤ f (fun l => Y l + δ * c47E L 0 l + a' * c47E L j l)
        - f (fun l => Y l + δ * c47E L 0 l + a * c47E L j l) := by
  have hV : (fun l => Y l + a * c47E L j l) ∈ ZipkinLostSales.LNatural.V L :=
    c47l_memV Y _ hY (c47l_smulE_anti L j a ha) (fun i => mul_nonneg ha (c47E_nonneg L j i))
  have H : f (fun i => Y i + a * c47E L j i + (a' - a) * c47E L j i)
      + f (fun i => Y i + a * c47E L j i + δ * c47E L 0 i)
      ≤ f (fun i => Y i + a * c47E L j i + δ * c47E L 0 i + (a' - a) * c47E L j i)
        + f (fun i => Y i + a * c47E L j i) :=
    c47l_incr hf j 0 (Nat.zero_le j) _ hV δ (a' - a) hδ (by linarith)
  have e1 : (fun i => Y i + a * c47E L j i + (a' - a) * c47E L j i)
      = fun l => Y l + a' * c47E L j l := by funext i; ring
  have e2 : (fun i => Y i + a * c47E L j i + δ * c47E L 0 i)
      = fun l => Y l + δ * c47E L 0 l + a * c47E L j l := by funext i; ring
  have e3 : (fun i => Y i + a * c47E L j i + δ * c47E L 0 i + (a' - a) * c47E L j i)
      = fun l => Y l + δ * c47E L 0 l + a' * c47E L j l := by funext i; ring
  rw [e3, e1, e2] at H
  linarith

/-- The Chebyshev step for `W^j` (E-index `j`). -/
theorem c47m_cheb {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M)
    (HL : ∀ n, ZipkinLostSales.LNatural.LNatConvexOn (ZipkinLostSales.LNatural.V (m + 1))
      (c47fb M n))
    (k j : ℕ) (hj : j ≤ m) (Y : Fin (m + 1) → ℝ) (hY : Y ∈ ZipkinLostSales.LNatural.V (m + 1))
    {z : ℝ} (hz : 0 ≤ z) {t : ℝ} (ht : 0 ≤ t) (mf : ℝ → ℝ) (hmf : Antitone mf)
    (hmt : ∀ d, mf d ∈ Set.Icc 0 t) :
    ∫ d, c47W M k j (fun l => nextZ Y d z l + (∫ d', mf d' ∂M.μ) * c47E (m + 1) j l) ∂M.μ
      ≤ ∫ d, c47W M k j (fun l => nextZ Y d z l + mf d * c47E (m + 1) j l) ∂M.μ := by
  haveI := hM.prob
  obtain ⟨K, hK⟩ := c47m_psi_bd M hM k j (by omega) j Y z ht
  have hcont := c47m_psi_cont M hM k j (by omega) j Y z
  have hB : ∀ d a, c47Bdf M j (fun l => nextZ Y d z l + a * c47E (m + 1) j l)
      = c47Bdf M j (nextZ Y d z) := fun d a => c47k_Bdf_inv M j j _ a le_rfl (by omega)
  refine c47l_chebstep M.μ hM.integrable
    (fun d a => c47W M k j (fun l => nextZ Y d z l + a * c47E (m + 1) j l)) mf t hcont
    ?_ ?_ hmf hmt K hK
  · intro d
    have hYd := c47m_nextZ_memV Y hY d hz
    refine c47l_convex_of_mid (hcont.comp (continuous_const.prodMk continuous_id)).continuousOn ?_
    intro x h hh hxh _
    have H := c47m_mid (HL (k + j)) j _ hYd x h hh hxh
    simp only [c47W, hB]
    linarith
  · intro d d' a a' hdd haa ha _
    have hδ := c47m_dd_nonneg (vext Y 0 - vext Y 1) d d' hdd
    have H := c47m_sub (HL (k + j)) j _ (c47m_nextZ_memV Y hY d' hz) _ a a' hδ ha.1 haa
    have e : ∀ b : ℝ, (fun l => nextZ Y d z l + b * c47E (m + 1) j l)
        = fun l => nextZ Y d' z l + (max (vext Y 0 - vext Y 1 - d) 0
          - max (vext Y 0 - vext Y 1 - d') 0) * c47E (m + 1) 0 l + b * c47E (m + 1) j l := by
      intro b; funext l
      simp only [nextZ, c47E]
      split_ifs <;> first | omega | ring
    simp only [c47W, hB]
    rw [e a, e a']
    linarith

/-- Q(j) as a predicate. -/
def c47Q {m : ℕ} (M : Data) (k j : ℕ) : Prop :=
  ∀ Y : Fin (m + 1) → ℝ, Y ∈ ZipkinLostSales.LNatural.V (m + 1) → ∀ t : ℝ, 0 ≤ t →
    c47W M k (j + 1) (fun l => Y l + c47mr M t j Y * c47E (m + 1) (j + 1) l)
      ≤ c47W M k (j + 1) (fun l => Y l + t * c47E (m + 1) j l)

theorem c47m_core {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M)
    (HL : ∀ n, ZipkinLostSales.LNatural.LNatConvexOn (ZipkinLostSales.LNatural.V (m + 1))
      (c47fb M n))
    (k j : ℕ) (hj : j ≤ m) (hQ : ∀ j', j' + 1 = j → c47Q (m := m) M k j')
    (Y : Fin (m + 1) → ℝ) (hY : Y ∈ ZipkinLostSales.LNatural.V (m + 1)) {t : ℝ} (ht : 0 ≤ t)
    {z : ℝ} (hz : 0 ≤ z) :
    ∫ d, c47W M k j (fun l => nextZ Y d z l + c47mr M t j Y * c47E (m + 1) j l) ∂M.μ
      ≤ ∫ d, c47W M k j (nextZ (fun l => Y l + t * c47E (m + 1) j l) d z) ∂M.μ := by
  haveI := hM.prob
  cases j with
  | zero =>
    simp_rw [c47m_nextZ_E0 Y t _ z]
    exact c47m_cheb M hM HL k 0 (Nat.zero_le _) Y hY hz ht (c47eps Y t) (c47m_eps_anti Y ht)
      (c47m_eps_mem Y ht)
  | succ j' =>
    have hj' : j' < m := by omega
    have e : ∀ d, nextZ (fun l => Y l + t * c47E (m + 1) (j' + 1) l) d z
        = fun l => nextZ Y d z l + t * c47E (m + 1) j' l := fun d => by
      have h := c47k_nextZ_E Y t d z (j' + 1) (by omega) (by omega)
      rwa [Nat.add_sub_cancel] at h
    simp_rw [e]
    have hQd : ∀ d, c47W M k (j' + 1)
          (fun l => nextZ Y d z l + c47mr M t j' (nextZ Y d z) * c47E (m + 1) (j' + 1) l)
        ≤ c47W M k (j' + 1) (fun l => nextZ Y d z l + t * c47E (m + 1) j' l) :=
      fun d => hQ j' rfl (nextZ Y d z) (c47m_nextZ_memV Y hY d hz) t ht
    have hanti : Antitone (fun d => c47mr M t j' (nextZ Y d z)) := by
      intro d d' hdd
      show c47mr M t j' (nextZ Y d' z) ≤ c47mr M t j' (nextZ Y d z)
      rw [c47m_nextZ_d Y d d' z]
      exact (c47m_mr_props M ht j' _).2 _ (c47m_dd_nonneg _ d d' hdd)
    have hmem : ∀ d, c47mr M t j' (nextZ Y d z) ∈ Set.Icc 0 t :=
      fun d => (c47m_mr_props M ht j' _).1
    have hbar : ∫ d, c47mr M t j' (nextZ Y d z) ∂M.μ = c47mr M t (j' + 1) Y := by
      show _ = ∫ d, c47mr M t j' (nextZ Y d 0) ∂M.μ
      exact integral_congr_ae (Filter.Eventually.of_forall fun d => c47m_mr_z M t Y d z j' hj')
    have hc := c47m_cheb M hM HL k (j' + 1) hj Y hY hz ht _ hanti hmem
    rw [hbar] at hc
    refine hc.trans (integral_mono ?_ ?_ hQd)
    · exact c47m_psi_int M hM k (j' + 1) (by omega) (j' + 1) Y z ht _ hanti.measurable hmem
    · exact c47m_psi_int M hM k (j' + 1) (by omega) j' Y z ht (fun _ => t) measurable_const
        (fun _ => ⟨ht, le_rfl⟩)

theorem c47m_Qstep {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M) (k j : ℕ) (hj : j < m)
    (Y : Fin (m + 1) → ℝ) (t mbar : ℝ)
    (hcore : ∀ z : ℝ, 0 ≤ z →
      ∫ d, c47W M k j (fun l => nextZ Y d z l + mbar * c47E (m + 1) j l) ∂M.μ
        ≤ ∫ d, c47W M k j (nextZ (fun l => Y l + t * c47E (m + 1) j l) d z) ∂M.μ) :
    c47W M k (j + 1) (fun l => Y l + mbar * c47E (m + 1) (j + 1) l)
      ≤ c47W M k (j + 1) (fun l => Y l + t * c47E (m + 1) j l) := by
  have e : ∀ d z, nextZ (fun l => Y l + mbar * c47E (m + 1) (j + 1) l) d z
      = fun l => nextZ Y d z l + mbar * c47E (m + 1) j l := fun d z => by
    have h := c47k_nextZ_E Y mbar d z (j + 1) (by omega) (by omega)
    rwa [Nat.add_sub_cancel] at h
  have hb := c47m_W_bdd M hM k j (by omega) (fun l => Y l + mbar * c47E (m + 1) (j + 1) l)
  rw [c47m_Wrec M hM k j (by omega) (fun l => Y l + mbar * c47E (m + 1) (j + 1) l),
    c47m_Wrec M hM k j (by omega) (fun l => Y l + t * c47E (m + 1) j l)]
  simp_rw [e] at hb ⊢
  haveI : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.mem_Ici.mpr le_rfl⟩⟩
  refine (add_le_add_iff_left _).mpr (le_ciInf fun z => (ciInf_le hb z).trans ?_)
  exact mul_le_mul_of_nonneg_left (hcore z z.2) hM.hγ0.le

theorem c47m_chain {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M)
    (HL : ∀ n, ZipkinLostSales.LNatural.LNatConvexOn (ZipkinLostSales.LNatural.V (m + 1))
      (c47fb M n)) (k : ℕ) : ∀ j, j < m → c47Q (m := m) M k j := by
  intro j
  induction j with
  | zero =>
    intro hj Y hY t ht
    exact c47m_Qstep M hM k 0 hj Y t _ (fun z hz =>
      c47m_core M hM HL k 0 (by omega) (fun j' h => absurd h (by omega)) Y hY ht hz)
  | succ j ih =>
    intro hj Y hY t ht
    exact c47m_Qstep M hM k (j + 1) hj Y t _ (fun z hz =>
      c47m_core M hM HL k (j + 1) (by omega)
        (fun j' h => by
          obtain rfl : j' = j := by omega
          exact ih (by omega)) Y hY ht hz)

theorem c47m_final {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M)
    (HL : ∀ n, ZipkinLostSales.LNatural.LNatConvexOn (ZipkinLostSales.LNatural.V (m + 1))
      (c47fb M n)) (k : ℕ) (Y : Fin (m + 1) → ℝ) (hY : Y ∈ ZipkinLostSales.LNatural.V (m + 1))
    {t : ℝ} (ht : 0 ≤ t) :
    c47W M k (m + 1) Y ≤ c47W M k (m + 1) (fun l => Y l + t * c47E (m + 1) m l) := by
  haveI := hM.prob
  haveI : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.mem_Ici.mpr le_rfl⟩⟩
  have hmb : 0 ≤ c47mr M t m Y := (c47m_mr_props M ht m Y).1.1
  rw [c47m_Wrec M hM k m le_rfl Y, c47m_Wrec M hM k m le_rfl (fun l => Y l + t * c47E (m + 1) m l)]
  refine (add_le_add_iff_left _).mpr (le_ciInf fun z => ?_)
  have hc := c47m_core M hM HL k m le_rfl
    (fun j' h => c47m_chain M hM HL k j' (by omega)) Y hY ht z.2
  have e : ∀ d, (fun l => nextZ Y d (z : ℝ) l + c47mr M t m Y * c47E (m + 1) m l)
      = nextZ Y d ((z : ℝ) + c47mr M t m Y) := fun d => by
    funext l
    have hl : (l : ℕ) ≤ m := Nat.lt_succ_iff.mp l.2
    simp only [nextZ, c47E, hl, if_true]
    ring
  simp_rw [e] at hc
  calc (⨅ z' : Set.Ici (0 : ℝ), M.γ * ∫ d, c47W M k m (nextZ Y d z') ∂M.μ)
      ≤ M.γ * ∫ d, c47W M k m (nextZ Y d ((z : ℝ) + c47mr M t m Y)) ∂M.μ :=
        ciInf_le (c47m_W_bdd M hM k m le_rfl Y) ⟨(z : ℝ) + c47mr M t m Y,
          Set.mem_Ici.mpr (add_nonneg z.2 hmb)⟩
    _ ≤ _ := mul_le_mul_of_nonneg_left hc hM.hγ0.le

/-- Property A: `fB_k(Y + t·1) ≥ fB_k(Y)` on `V`, given L♮-convexity of every `c47fb M n`. -/
theorem c47m_A {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M)
    (HL : ∀ n, ZipkinLostSales.LNatural.LNatConvexOn (ZipkinLostSales.LNatural.V (m + 1))
      (c47fb M n)) (k : ℕ) (Y : Fin (m + 1) → ℝ) (hY : Y ∈ ZipkinLostSales.LNatural.V (m + 1))
    {t : ℝ} (ht : 0 ≤ t) : fB M k Y ≤ fB M k (fun l => Y l + t) := by
  have e : (fun l => Y l + t) = fun l => Y l + t * c47E (m + 1) m l := by
    funext l
    have hl : (l : ℕ) ≤ m := Nat.lt_succ_iff.mp l.2
    simp [c47E, hl]
  have h1 := c47j_ident M hM k Y
  have h2 := c47j_ident M hM k (fun l => Y l + t * c47E (m + 1) m l)
  have h3 := c47m_final M hM HL k Y hY ht
  unfold c47W at h3
  rw [e]
  linarith

/-! Final glue (session 10): L♮-convexity from `LNatural.theorem_4` (with `c = 0`,
`hh' = hh + (1-γ)c`, `p' = p - c`), property A, child C, and the parent. -/

theorem c47m_HL {m : ℕ} (M : Data) (hM : Assumptions (m + 1) M) (n : ℕ) :
    ZipkinLostSales.LNatural.LNatConvexOn (ZipkinLostSales.LNatural.V (m + 1)) (c47fb M n) := by
  haveI := hM.prob
  exact (ZipkinLostSales.LNatural.theorem_4 (m + 1) (Nat.succ_pos m) M.μ hM.demand_nonneg
    hM.integrable 0 (M.hh + (1 - M.γ) * M.c) (M.p - M.c) M.γ le_rfl
    (add_nonneg hM.hhh (mul_nonneg (by linarith [hM.hγ1]) hM.hc))
    (by linarith [hM.hph]) hM.hγ0 hM.hγ1 n).1

theorem childC_of_A {L : ℕ} (M : Data) (hM : Assumptions L M) (k : ℕ)
    (hA : ∀ w : Fin L → ℝ, w ∈ ZipkinLostSales.LNatural.V L → ∀ t : ℝ, 0 ≤ t →
      fB M k w ≤ fB M k (fun l => w l + t))
    (v : Fin L → ℝ) (hv : v ∈ ZipkinLostSales.LNatural.V L) (z₁ z₂ : ℝ) (h0 : 0 ≤ z₁)
    (h12 : z₁ ≤ z₂) :
    ∫ d, fB M k (nextZ v d z₁) ∂M.μ ≤ ∫ d, fB M k (nextZ v d z₂) ∂M.μ := by
  haveI := hM.prob
  obtain ⟨B, C, hB, hC, hlow, hlip⟩ := c47_fB_props M hM k
  have hfc : Continuous (fB (L := L) M k) := by
    have : LipschitzWith ⟨C, hC⟩ (fB (L := L) M k) := LipschitzWith.of_dist_le_mul (fun a b => by
      rw [Real.dist_eq, dist_eq_norm]; exact hlip a b)
    exact this.continuous
  have hpt : ∀ d, fB M k (nextZ v d z₁) ≤ fB M k (nextZ v d z₂) := by
    intro d
    have he : nextZ v d z₂ = fun l => nextZ v d z₁ l + (z₂ - z₁) := by
      funext l; simp only [nextZ]; ring
    rw [he]
    exact hA _ (c47m_nextZ_memV v hv d h0) _ (by linarith)
  have hdiff : Integrable (fun d => fB M k (nextZ v d z₂) - fB M k (nextZ v d z₁)) M.μ := by
    refine (integrable_const (C * |z₂ - z₁|)).mono'
      (((hfc.comp (c47_nextZ_cont v z₂)).sub (hfc.comp (c47_nextZ_cont v z₁))).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun d => ?_))
    rw [Real.norm_eq_abs]
    exact le_trans (hlip _ _) (mul_le_mul_of_nonneg_left (c47_nextZ_z v d z₂ z₁) hC)
  by_cases hi : Integrable (fun d => fB M k (nextZ v d z₁)) M.μ
  · have hi2 : Integrable (fun d => fB M k (nextZ v d z₂)) M.μ :=
      (hi.add hdiff).congr (Filter.Eventually.of_forall (fun d => by simp))
    exact integral_mono hi hi2 hpt
  · have hi2 : ¬ Integrable (fun d => fB M k (nextZ v d z₂)) M.μ := fun h2 =>
      hi ((h2.sub hdiff).congr (Filter.Eventually.of_forall (fun d => by simp)))
    rw [integral_undef hi, integral_undef hi2]

open ZipkinLostSales.Bounds in
theorem solution {L : ℕ} (M : Data) (hM : Assumptions L M) (k : ℕ) (v : Fin L → ℝ)
    (hv : v ∈ ZipkinLostSales.LNatural.V L) : ∃ z : ℝ, IsOptOrder M k v z ∧ InZ L M v z := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by have := hM.hL; omega⟩
  exact assembly M hM k v hv (childA_gB_continuousOn M hM k v hv)
    (fun z₁ z₂ h0 h12 hb => childB_q_mono_beyond M hM v hv z₁ z₂ h0 h12 hb)
    (fun z₁ z₂ h0 h12 => childC_of_A M hM k
      (fun w hw t ht => c47m_A M hM (c47m_HL M hM) k w hw ht) v hv z₁ z₂ h0 h12)
