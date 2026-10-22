-- Prove2me | solution 1 for ZipkinLostSales.Bounds.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:45:59.847003+00:00
-- url     : https://prove2.me/submissions/1d843781-bacf-457a-bfd2-f46258d37738

import Mathlib
import Definitions.Def_ZipkinLostSales_Bounds_Model



namespace ZipkinLostSales.Bounds

namespace L6

open MeasureTheory ZipkinLostSales.LNatural

variable {L : ℕ}

lemma vext_ge (v : Fin L → ℝ) (l : ℕ) (hl : L ≤ l) : vext v l = 0 := by
  simp [vext, show ¬ l < L by omega]

lemma vext_le_sum (v : Fin L → ℝ) (l : ℕ) : |vext v l| ≤ ∑ i, |v i| := by
  unfold vext
  split_ifs with h
  · exact Finset.single_le_sum (f := fun i => |v i|) (fun i _ => abs_nonneg _) (Finset.mem_univ _)
  · simp only [abs_zero]; exact Finset.sum_nonneg fun i _ => abs_nonneg _

lemma onHand_indep (v : Fin L → ℝ) (z : ℝ) (D : Fin L → ℝ) :
    ∀ j, j < L → onHand v z D j = onHand v 0 D j := by
  intro j
  induction j with
  | zero => intro h; simp [onHand, arrival, h]
  | succ j ih =>
    intro h
    simp only [onHand, arrival, if_pos h]
    rw [ih (by omega)]

lemma yPlusL_shift (hL : 0 < L) (v : Fin L → ℝ) (z : ℝ) (D : Fin L → ℝ) :
    yPlusL v z D = yPlusL v 0 D + z := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  simp only [yPlusL, onHand, arrival, lt_irrefl, if_false]
  rw [onHand_indep v z D m (by omega)]
  ring

/-- `W j = y_{t+j} + v_{j+1}` with zero current order. -/
noncomputable def W (v : Fin L → ℝ) (D : Fin L → ℝ) (j : ℕ) : ℝ :=
  onHand v 0 D j + vext v (j + 1)

lemma W_zero (hL : 0 < L) (v : Fin L → ℝ) (D : Fin L → ℝ) : W v D 0 = vext v 0 := by
  simp [W, onHand, arrival, hL, xext]

lemma W_succ (v : Fin L → ℝ) (D : Fin L → ℝ) (j : ℕ) (hj : j < L) :
    W v D (j + 1) = max (W v D j - vext D j) (vext v (j + 1)) := by
  have harr : arrival v 0 (j + 1) = vext v (j + 1) - vext v (j + 1 + 1) := by
    unfold arrival
    split_ifs with h
    · rfl
    · rw [vext_ge v (j + 1) (by omega), vext_ge v (j + 1 + 1) (by omega)]; ring
  have key := max_add_add_right (onHand v 0 D j - vext D j) 0 (vext v (j + 1))
  simp only [zero_add] at key
  simp only [W, onHand, harr]
  rw [show onHand v 0 D j + vext v (j + 1) - vext D j = onHand v 0 D j - vext D j + vext v (j + 1)
    by ring, key]
  ring

lemma W_ge_self (hL : 0 < L) (v : Fin L → ℝ) (D : Fin L → ℝ) (j : ℕ) (hj : j ≤ L) :
    vext v j ≤ W v D j := by
  cases j with
  | zero => rw [W_zero hL]
  | succ j => rw [W_succ v D j (by omega)]; exact le_max_right _ _

lemma W_ge (hL : 0 < L) (v : Fin L → ℝ) (D : Fin L → ℝ) (l : ℕ) :
    ∀ j, l ≤ j → j ≤ L → vext v l - ∑ i ∈ Finset.Ico l j, vext D i ≤ W v D j := by
  intro j
  induction j with
  | zero =>
    intro h1 h2
    have : l = 0 := by omega
    subst this
    simp [W_ge_self hL v D 0 h2]
  | succ j ih =>
    intro h1 h2
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · subst h; simp [W_ge_self hL v D _ h2]
    · rw [Finset.sum_Ico_succ_top (by omega), W_succ v D j (by omega)]
      have := ih (by omega) (by omega)
      have := le_max_left (W v D j - vext D j) (vext v (j + 1))
      linarith

lemma W_le (hL : 0 < L) (v : Fin L → ℝ) (D : Fin L → ℝ) :
    ∀ j, j ≤ L → W v D j ≤ ∑ i, |v i| + ∑ i ∈ Finset.range j, |vext D i| := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [W_zero hL]; simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    exact (le_abs_self _).trans (vext_le_sum v 0)
  | succ j ih =>
    intro h
    rw [W_succ v D j (by omega), Finset.sum_range_succ]
    have h1 := ih (by omega)
    have h2 := (le_abs_self _).trans (vext_le_sum v (j + 1))
    have h3 := neg_abs_le (vext D j)
    have h4 : 0 ≤ ∑ i ∈ Finset.range j, |vext D i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have h5 := abs_nonneg (vext D j)
    apply max_le <;> linarith

/-- `Y(D) = y_{+L}` with zero current order. -/
noncomputable def Y (v : Fin L → ℝ) (D : Fin L → ℝ) : ℝ := yPlusL v 0 D

lemma Y_eq_W (v : Fin L → ℝ) (D : Fin L → ℝ) : Y v D = W v D L := by
  simp [Y, yPlusL, W, vext_ge v (L + 1) (by omega)]

lemma Y_nonneg (hL : 0 < L) (v : Fin L → ℝ) (D : Fin L → ℝ) : 0 ≤ Y v D := by
  rw [Y_eq_W]
  have := W_ge_self hL v D L le_rfl
  rwa [vext_ge v L le_rfl] at this

lemma Y_ge (hL : 0 < L) (v : Fin L → ℝ) (D : Fin L → ℝ) (l : ℕ) (hl : l ≤ L) :
    vext v l - ∑ i ∈ Finset.Ico l L, vext D i ≤ Y v D := by
  rw [Y_eq_W]; exact W_ge hL v D l L hl le_rfl

lemma Y_le (hL : 0 < L) (v : Fin L → ℝ) (D : Fin L → ℝ) :
    Y v D ≤ ∑ i, |v i| + ∑ i, |D i| := by
  rw [Y_eq_W]
  refine (W_le hL v D L le_rfl).trans ?_
  gcongr
  rw [← Fin.sum_univ_eq_sum_range (fun i => |vext D i|)]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i _
  simp [vext]

lemma measurable_vext (j : ℕ) : Measurable fun D : Fin L → ℝ => vext D j := by
  unfold vext
  split_ifs with h
  · exact measurable_pi_apply _
  · exact measurable_const

lemma measurable_onHand (v : Fin L → ℝ) (z : ℝ) :
    ∀ j, Measurable fun D : Fin L → ℝ => onHand v z D j := by
  intro j
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    simp only [onHand]
    exact ((ih.sub (measurable_vext j)).max measurable_const).add_const _

lemma measurable_Y (v : Fin L → ℝ) : Measurable fun D : Fin L → ℝ => Y v D :=
  measurable_onHand v 0 L

section Q0

variable (M : Data)

lemma integrable_max_sub (hM : Assumptions L M) (y : ℝ) :
    Integrable (fun d => max (y - d) 0) M.μ := by
  haveI := hM.prob
  refine Integrable.mono' ((integrable_const |y|).add hM.integrable.abs) ?_ ?_
  · exact ((measurable_const.sub measurable_id).max measurable_const).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun d => ?_
    simp only [Real.norm_eq_abs, id, Pi.add_apply]
    rw [abs_le]; constructor
    · have := le_max_right (y - d) 0; have := abs_nonneg y; have := abs_nonneg d; linarith
    · apply max_le
      · have := le_abs_self y; have := neg_abs_le d; linarith
      · positivity

lemma integrable_max_sub' (hM : Assumptions L M) (y : ℝ) :
    Integrable (fun d => max (d - y) 0) M.μ := by
  haveI := hM.prob
  refine Integrable.mono' ((integrable_const |y|).add hM.integrable.abs) ?_ ?_
  · exact ((measurable_id.sub measurable_const).max measurable_const).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun d => ?_
    simp only [Real.norm_eq_abs, id, Pi.add_apply]
    rw [abs_le]; constructor
    · have := le_max_right (d - y) 0; have := abs_nonneg y; have := abs_nonneg d; linarith
    · apply max_le
      · have := neg_abs_le y; have := le_abs_self d; linarith
      · positivity

lemma int_pos_part (hM : Assumptions L M) (y : ℝ) :
    ∫ d, max (y - d) 0 ∂M.μ = y - ∫ d, d ∂M.μ + ∫ d, max (d - y) 0 ∂M.μ := by
  haveI := hM.prob
  have h1 : (fun d => max (y - d) 0) = fun d => (y - d) + max (d - y) 0 := by
    funext d; rcases le_total y d with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hid : Integrable (fun d : ℝ => d) M.μ := hM.integrable
  have hi1 : Integrable (fun d : ℝ => y - d) M.μ := (integrable_const y).sub hid
  rw [h1, integral_add hi1 (integrable_max_sub' M hM y),
    integral_sub (integrable_const y) hid, integral_const]
  simp

lemma hpos (hM : Assumptions L M) : 0 < M.p + M.h := by
  have := hM.hch; have := hM.hph; linarith

lemma q0_diff (hM : Assumptions L M) {y1 y2 : ℝ} (h : y1 ≤ y2) :
    (y2 - y1) * ((M.c + M.h) - (M.p + M.h) * M.μ.real (Set.Ioi y1)) ≤ q0 M y2 - q0 M y1 ∧
      q0 M y2 - q0 M y1 ≤ (y2 - y1) * ((M.c + M.h) - (M.p + M.h) * M.μ.real (Set.Ici y2)) := by
  haveI := hM.prob
  set k : ℝ → ℝ := fun d => max (d - y1) 0 - max (d - y2) 0 with hk
  have hki : Integrable k M.μ := (integrable_max_sub' M hM y1).sub (integrable_max_sub' M hM y2)
  have hq : q0 M y2 - q0 M y1 = (M.c + M.h) * (y2 - y1) - (M.p + M.h) * ∫ d, k d ∂M.μ := by
    unfold q0
    rw [int_pos_part M hM y2, int_pos_part M hM y1, hk,
      integral_sub (integrable_max_sub' M hM y1) (integrable_max_sub' M hM y2)]
    ring
  have hlow : ∀ d, (y2 - y1) * (Set.Ici y2).indicator 1 d ≤ k d := by
    intro d
    simp only [hk, Set.indicator_apply, Set.mem_Ici, Pi.one_apply]
    split_ifs with hd
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · have := le_max_right (d - y1) 0
      rw [max_eq_right (by linarith : d - y2 ≤ 0)]; linarith
  have hup : ∀ d, k d ≤ (y2 - y1) * (Set.Ioi y1).indicator 1 d := by
    intro d
    simp only [hk, Set.indicator_apply, Set.mem_Ioi, Pi.one_apply]
    split_ifs with hd
    · have := le_max_left (d - y2) 0; have := le_max_right (d - y2) 0
      rcases le_total (d - y1) 0 with h' | h'
      · rw [max_eq_right h']; linarith
      · rw [max_eq_left h']; linarith
    · rw [max_eq_right (by linarith : d - y1 ≤ 0), max_eq_right (by linarith : d - y2 ≤ 0)]
      simp
  have hI1 : (y2 - y1) * M.μ.real (Set.Ici y2) ≤ ∫ d, k d ∂M.μ := by
    have := integral_mono ((integrable_indicator_iff measurableSet_Ici).2
      (integrable_const (1:ℝ)).integrableOn |>.const_mul (y2 - y1)) hki hlow
    rwa [integral_const_mul, integral_indicator_const _ measurableSet_Ici, smul_eq_mul, mul_one] at this
  have hI2 : ∫ d, k d ∂M.μ ≤ (y2 - y1) * M.μ.real (Set.Ioi y1) := by
    have := integral_mono hki ((integrable_indicator_iff measurableSet_Ioi).2
      (integrable_const (1:ℝ)).integrableOn |>.const_mul (y2 - y1)) hup
    rwa [integral_const_mul, integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_one] at this
  have hp := hpos M hM
  rw [hq]
  constructor <;> nlinarith

lemma q0_lip (hM : Assumptions L M) (y1 y2 : ℝ) :
    |q0 M y2 - q0 M y1| ≤ ((M.c + M.h) + (M.p + M.h)) * |y2 - y1| := by
  haveI := hM.prob
  have hp := hpos M hM
  have hc := hM.hch
  have key : ∀ a b : ℝ, a ≤ b → |q0 M b - q0 M a| ≤ ((M.c + M.h) + (M.p + M.h)) * (b - a) := by
    intro a b hab
    obtain ⟨h1, h2⟩ := q0_diff M hM hab
    have m1 : M.μ.real (Set.Ioi a) ≤ 1 := measureReal_le_one
    have m2 : 0 ≤ M.μ.real (Set.Ici b) := measureReal_nonneg
    have m3 : 0 ≤ M.μ.real (Set.Ioi a) := measureReal_nonneg
    have hba : 0 ≤ b - a := by linarith
    have e1 := mul_le_mul_of_nonneg_left m1 (mul_nonneg hba hp.le)
    have e2 := mul_nonneg (mul_nonneg hba hp.le) m2
    have e3 := mul_nonneg hba hc.le
    have e4 := mul_nonneg hba hp.le
    rw [abs_le]; constructor <;> nlinarith
  rcases le_total y1 y2 with h | h
  · rw [abs_of_nonneg (by linarith : 0 ≤ y2 - y1)]; exact key _ _ h
  · rw [abs_sub_comm, abs_sub_comm y2, abs_of_nonneg (by linarith : 0 ≤ y1 - y2)]
    exact key _ _ h

lemma q0_continuous (hM : Assumptions L M) : Continuous (q0 M) := by
  have hK : 0 ≤ (M.c + M.h) + (M.p + M.h) := by have := hpos M hM; have := hM.hch; linarith
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal ((M.c + M.h) + (M.p + M.h)))
    fun x y => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK]
  exact q0_lip M hM y x

lemma int_aff {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : α → ℝ) (hf : Integrable f ν) (a b c : ℝ) :
    ∫ x, a * (b - c * f x) ∂ν = a * (b - c * ∫ x, f x ∂ν) := by
  rw [integral_const_mul, integral_sub (integrable_const b) (hf.const_mul c), integral_const,
    integral_const_mul]
  simp

variable (L) in
/-- The joint law of the demands of periods `t, …, t+L-1`. -/
noncomputable def P : Measure (Fin L → ℝ) := Measure.pi fun _ => M.μ

lemma P_prob (hM : Assumptions L M) : IsProbabilityMeasure (P L M) := by
  haveI := hM.prob; unfold P; infer_instance

noncomputable def phi (v : Fin L → ℝ) (z : ℝ) : ℝ := ∫ D, q0 M (Y v D + z) ∂(P L M)

noncomputable def G (v : Fin L → ℝ) (z : ℝ) : ℝ := ∫ D, M.μ.real (Set.Ioi (Y v D + z)) ∂(P L M)

noncomputable def H (v : Fin L → ℝ) (z : ℝ) : ℝ := ∫ D, M.μ.real (Set.Ici (Y v D + z)) ∂(P L M)

lemma integrable_q0Y (hM : Assumptions L M) (v : Fin L → ℝ) (z : ℝ) :
    Integrable (fun D => q0 M (Y v D + z)) (P L M) := by
  haveI := hM.prob
  haveI := P_prob M hM
  set K := (M.c + M.h) + (M.p + M.h) with hKdef
  have hK : 0 ≤ K := by have := hpos M hM; have := hM.hch; linarith
  have hi : Integrable (fun D : Fin L → ℝ => ∑ i, |D i|) (P L M) :=
    integrable_finset_sum _ (fun i _ => (integrable_eval (i := i) hM.integrable).abs)
  refine Integrable.mono' ((integrable_const (|q0 M 0| + K * (∑ i, |v i| + |z|))).add
    (hi.const_mul K)) ?_ ?_
  · exact ((q0_continuous M hM).measurable.comp ((measurable_Y v).add_const z)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun D => ?_
    simp only [Real.norm_eq_abs, Pi.add_apply]
    have h1 := q0_lip M hM 0 (Y v D + z)
    have h2 := Y_le hM.hL v D
    have h3 := Y_nonneg hM.hL v D
    have h4 : |Y v D + z - 0| ≤ ∑ i, |v i| + ∑ i, |D i| + |z| := by
      rw [sub_zero]; refine (abs_add_le _ _).trans ?_; rw [abs_of_nonneg h3]; linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hK
    have h6 := abs_sub_abs_le_abs_sub (q0 M (Y v D + z)) (q0 M 0)
    nlinarith

lemma tail_anti (hM : Assumptions L M) : Antitone fun y => M.μ.real (Set.Ioi y) := by
  haveI := hM.prob
  intro a b hab
  exact measureReal_mono (Set.Ioi_subset_Ioi hab)

lemma tail_anti' (hM : Assumptions L M) : Antitone fun y => M.μ.real (Set.Ici y) := by
  haveI := hM.prob
  intro a b hab
  exact measureReal_mono (Set.Ici_subset_Ici.2 hab)

lemma integrable_tail (hM : Assumptions L M) (v : Fin L → ℝ) (z : ℝ) :
    Integrable (fun D => M.μ.real (Set.Ioi (Y v D + z))) (P L M) := by
  haveI := hM.prob
  haveI := P_prob M hM
  refine Integrable.mono' (integrable_const 1) ?_ ?_
  · exact ((tail_anti M hM).measurable.comp ((measurable_Y v).add_const z)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun D => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one

lemma integrable_tail' (hM : Assumptions L M) (v : Fin L → ℝ) (z : ℝ) :
    Integrable (fun D => M.μ.real (Set.Ici (Y v D + z))) (P L M) := by
  haveI := hM.prob
  haveI := P_prob M hM
  refine Integrable.mono' (integrable_const 1) ?_ ?_
  · exact ((tail_anti' M hM).measurable.comp ((measurable_Y v).add_const z)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun D => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one

lemma phi_diff (hM : Assumptions L M) (v : Fin L → ℝ) {z1 z2 : ℝ} (h : z1 ≤ z2) :
    (z2 - z1) * ((M.c + M.h) - (M.p + M.h) * G M v z1) ≤ phi M v z2 - phi M v z1 ∧
      phi M v z2 - phi M v z1 ≤ (z2 - z1) * ((M.c + M.h) - (M.p + M.h) * H M v z2) := by
  haveI := P_prob M hM
  unfold phi G H
  rw [← integral_sub (integrable_q0Y M hM v z2) (integrable_q0Y M hM v z1),
    ← int_aff _ _ (integrable_tail M hM v z1), ← int_aff _ _ (integrable_tail' M hM v z2)]
  constructor
  · refine integral_mono (((integrable_const _).sub ((integrable_tail M hM v z1).const_mul _)).const_mul _)
      ((integrable_q0Y M hM v z2).sub (integrable_q0Y M hM v z1)) fun D => ?_
    have := (q0_diff M hM (y1 := Y v D + z1) (y2 := Y v D + z2) (by linarith)).1
    simp only at this ⊢
    rwa [show Y v D + z2 - (Y v D + z1) = z2 - z1 by ring] at this
  · refine integral_mono ((integrable_q0Y M hM v z2).sub (integrable_q0Y M hM v z1))
      (((integrable_const _).sub ((integrable_tail' M hM v z2).const_mul _)).const_mul _) fun D => ?_
    have := (q0_diff M hM (y1 := Y v D + z1) (y2 := Y v D + z2) (by linarith)).2
    simp only at this ⊢
    rwa [show Y v D + z2 - (Y v D + z1) = z2 - z1 by ring] at this

lemma G_le_H (hM : Assumptions L M) (v : Fin L → ℝ) (z : ℝ) : G M v z ≤ H M v z := by
  haveI := hM.prob
  exact integral_mono (integrable_tail M hM v z) (integrable_tail' M hM v z)
    fun D => measureReal_mono Set.Ioi_subset_Ici_self

lemma G_anti (hM : Assumptions L M) (v : Fin L → ℝ) : Antitone (G M v) := by
  intro a b hab
  exact integral_mono (integrable_tail M hM v b) (integrable_tail M hM v a)
    fun D => tail_anti M hM (by linarith : Y v D + a ≤ Y v D + b)

lemma G_nonneg (v : Fin L → ℝ) (z : ℝ) : 0 ≤ G M v z :=
  integral_nonneg fun _ => measureReal_nonneg

lemma H_le_one (hM : Assumptions L M) (v : Fin L → ℝ) (z : ℝ) : H M v z ≤ 1 := by
  haveI := hM.prob
  haveI := P_prob M hM
  have := integral_mono (integrable_tail' M hM v z) (integrable_const (1:ℝ))
    fun D => (measureReal_le_one : M.μ.real (Set.Ici (Y v D + z)) ≤ 1)
  simpa [H] using this

lemma G_le_tail (hM : Assumptions L M) (v : Fin L → ℝ) (z : ℝ) :
    G M v z ≤ M.μ.real (Set.Ioi z) := by
  haveI := hM.prob
  haveI := P_prob M hM
  have := integral_mono (integrable_tail M hM v z) (integrable_const (M.μ.real (Set.Ioi z)))
    fun D => tail_anti M hM (by have := Y_nonneg hM.hL v D; linarith : z ≤ Y v D + z)
  simpa [G] using this

end Q0

lemma tail_small (ν : Measure ℝ) [IsProbabilityMeasure ν] {ε : ℝ} (hε : 0 < ε) :
    ∃ z, 0 ≤ z ∧ ν.real (Set.Ioi z) ≤ ε := by
  have h := ProbabilityTheory.tendsto_cdf_atTop (μ := ν)
  have := h.eventually (lt_mem_nhds (by linarith : 1 - ε < 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 this
  refine ⟨max N 0, le_max_right _ _, ?_⟩
  have := hN (max N 0) (le_max_left _ _)
  rw [ProbabilityTheory.cdf_eq_real] at this
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]; linarith

section Opt

variable (M : Data)

lemma theta_pos (hM : Assumptions L M) : 0 < θbar M := div_pos hM.hch (hpos M hM)

lemma theta_lt_one (hM : Assumptions L M) : θbar M < 1 := by
  rw [θbar, div_lt_one (hpos M hM)]; exact hM.hph

lemma le_theta_iff (hM : Assumptions L M) (x : ℝ) :
    x ≤ θbar M ↔ (M.p + M.h) * x ≤ M.c + M.h := by
  rw [θbar, le_div_iff₀ (hpos M hM), mul_comm]

lemma theta_lt_iff (hM : Assumptions L M) (x : ℝ) :
    θbar M < x ↔ M.c + M.h < (M.p + M.h) * x := by
  rw [θbar, div_lt_iff₀ (hpos M hM), mul_comm]

/-- The least minimizer of `phi`, with the property that `G > θ̄` strictly below it. -/
lemma opt_exists (hM : Assumptions L M) (v : Fin L → ℝ) :
    ∃ zs : ℝ, IsLeast {z | 0 ≤ z ∧ ∀ z', 0 ≤ z' → phi M v z ≤ phi M v z'} zs ∧
      ∀ w, 0 ≤ w → w < zs → θbar M < G M v w := by
  haveI := hM.prob
  have hp := hpos M hM
  have hc := hM.hch
  set S := {z : ℝ | 0 ≤ z ∧ G M v z ≤ θbar M} with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨z, hz0, hz⟩ := tail_small M.μ (theta_pos M hM)
    exact ⟨z, hz0, (G_le_tail M hM v z).trans hz⟩
  have hSbdd : BddBelow S := ⟨0, fun z hz => hz.1⟩
  set zs := sInf S with hzs
  have h0 : 0 ≤ zs := le_csInf hSne fun z hz => hz.1
  have habove : ∀ w, zs < w → G M v w ≤ θbar M := by
    intro w hw
    obtain ⟨s, hs, hsw⟩ := exists_lt_of_csInf_lt hSne hw
    exact (G_anti M hM v hsw.le).trans hs.2
  have hbelow : ∀ w, 0 ≤ w → w < zs → θbar M < G M v w := by
    intro w hw0 hw
    by_contra hcon
    push_neg at hcon
    have := csInf_le hSbdd ⟨hw0, hcon⟩
    linarith
  have hH1 : ∀ z, 0 ≤ H M v z := fun z => integral_nonneg fun _ => measureReal_nonneg
  -- upper Lipschitz-type bound
  have hup : ∀ a b, a ≤ b → phi M v b - phi M v a ≤ (b - a) * (M.c + M.h) := by
    intro a b hab
    have := (phi_diff M hM v hab).2
    have := mul_nonneg (mul_nonneg (sub_nonneg.2 hab) hp.le) (hH1 b)
    nlinarith
  refine ⟨zs, ⟨⟨h0, fun z' hz' => ?_⟩, fun z hz => ?_⟩, hbelow⟩
  · rcases lt_trichotomy z' zs with hlt | heq | hgt
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      set u := zs - min ((zs - z') / 2) (ε / (M.c + M.h)) with hu
      have hm1 : min ((zs - z') / 2) (ε / (M.c + M.h)) ≤ (zs - z') / 2 := min_le_left _ _
      have hm2 : min ((zs - z') / 2) (ε / (M.c + M.h)) ≤ ε / (M.c + M.h) := min_le_right _ _
      have hm3 : 0 < min ((zs - z') / 2) (ε / (M.c + M.h)) :=
        lt_min (by linarith) (div_pos hε hc)
      have hu1 : z' < u := by linarith
      have hu2 : u < zs := by linarith
      have hGu := (theta_lt_iff M hM _).1 (hbelow u (by linarith) hu2)
      have hHu : (M.p + M.h) * G M v u ≤ (M.p + M.h) * H M v u :=
        mul_le_mul_of_nonneg_left (G_le_H M hM v u) hp.le
      have d1 := (phi_diff M hM v hu1.le).2
      have d2 := hup u zs hu2.le
      have e1 : (u - z') * (M.c + M.h - (M.p + M.h) * H M v u) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have e2 : (zs - u) * (M.c + M.h) ≤ ε := by
        rw [show zs - u = min ((zs - z') / 2) (ε / (M.c + M.h)) by rw [hu]; ring]
        calc _ ≤ ε / (M.c + M.h) * (M.c + M.h) := mul_le_mul_of_nonneg_right hm2 hc.le
          _ = ε := div_mul_cancel₀ _ hc.ne'
      linarith
    · rw [heq]
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      set w := zs + min ((z' - zs) / 2) (ε / (M.p + M.h)) with hw
      have hm1 : min ((z' - zs) / 2) (ε / (M.p + M.h)) ≤ (z' - zs) / 2 := min_le_left _ _
      have hm2 : min ((z' - zs) / 2) (ε / (M.p + M.h)) ≤ ε / (M.p + M.h) := min_le_right _ _
      have hm3 : 0 < min ((z' - zs) / 2) (ε / (M.p + M.h)) :=
        lt_min (by linarith) (div_pos hε hp)
      have hw1 : zs < w := by linarith
      have hw2 : w < z' := by linarith
      have hGw := (le_theta_iff M hM _).1 (habove w hw1)
      have d1 := (phi_diff M hM v hw2.le).1
      have d2 := (phi_diff M hM v hw1.le).1
      have hG1 : G M v zs ≤ 1 := (G_le_H M hM v zs).trans (H_le_one M hM v zs)
      have e3 : (w - zs) * ((M.p + M.h) * G M v zs) ≤ (w - zs) * (M.p + M.h) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        nlinarith
      have e1 : 0 ≤ (z' - w) * (M.c + M.h - (M.p + M.h) * G M v w) :=
        mul_nonneg (by linarith) (by linarith)
      have e2 : (w - zs) * (M.p + M.h) ≤ ε := by
        rw [show w - zs = min ((z' - zs) / 2) (ε / (M.p + M.h)) by rw [hw]; ring]
        calc _ ≤ ε / (M.p + M.h) * (M.p + M.h) := mul_le_mul_of_nonneg_right hm2 hp.le
          _ = ε := div_mul_cancel₀ _ hp.ne'
      nlinarith
  · by_contra hcon
    push_neg at hcon
    obtain ⟨hz0, hzmin⟩ := hz
    set u := (z + zs) / 2 with hu
    have hu1 : z < u := by linarith
    have hu2 : u < zs := by linarith
    have hGu := (theta_lt_iff M hM _).1 (hbelow u (by linarith) hu2)
    have hHu : (M.p + M.h) * G M v u ≤ (M.p + M.h) * H M v u :=
      mul_le_mul_of_nonneg_left (G_le_H M hM v u) hp.le
    have d1 := (phi_diff M hM v hu1.le).2
    have e1 : (u - z) * (M.c + M.h - (M.p + M.h) * H M v u) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    have := hzmin u (by linarith)
    linarith

end Opt

section Frac

variable (M : Data)

/-- `S_l(D) = d_{[l, L-1]}`. -/
noncomputable def Sl (l : ℕ) (D : Fin L → ℝ) : ℝ := ∑ n ∈ Finset.Ico l L, vext D n

lemma measurable_Sl (l : ℕ) : Measurable fun D : Fin L → ℝ => Sl l D :=
  Finset.measurable_sum _ fun n _ => measurable_vext n

lemma Sl_eq (l : ℕ) (D : Fin L → ℝ) :
    Sl l D = ∑ i : Fin L, if l ≤ (i : ℕ) then D i else 0 := by
  have h1 : (∑ i : Fin L, if l ≤ (i : ℕ) then D i else 0) =
      ∑ i : Fin L, (fun n : ℕ => if l ≤ n then vext D n else 0) (i : ℕ) := by
    apply Finset.sum_congr rfl; intro i _; simp [vext]
  rw [h1, Fin.sum_univ_eq_sum_range (fun n : ℕ => if l ≤ n then vext D n else 0) L,
    ← Finset.sum_filter, Sl]
  congr 1
  ext n; simp [and_comm]

lemma sum_Ici_eq (l : Fin (L + 1)) (D' : Fin (L + 1) → ℝ) :
    ∑ j ∈ Finset.Ici l, D' j = D' (Fin.last L) + Sl (l : ℕ) (fun i => D' (Fin.castSucc i)) := by
  have h1 : ∑ j ∈ Finset.Ici l, D' j = ∑ j : Fin (L + 1), if l ≤ j then D' j else 0 := by
    rw [← Finset.sum_filter]; congr 1; ext j; simp
  rw [h1, Fin.sum_univ_castSucc, Sl_eq, add_comm]
  congr 1
  all_goals first
    | simp [Fin.le_last]
    | (apply Finset.sum_congr rfl; intro i _; simp [Fin.le_iff_val_le_val])

/-- The tail probability defining `s̄_l`. -/
noncomputable def T (l : Fin (L + 1)) (s : ℝ) : ℝ :=
  ((Measure.pi fun _ : Fin (L + 1) => M.μ) {D | s < ∑ j ∈ Finset.Ici l, D j}).toReal

lemma measurable_sumIci (l : Fin (L + 1)) :
    Measurable fun D : Fin (L + 1) → ℝ => ∑ j ∈ Finset.Ici l, D j :=
  Finset.measurable_sum _ fun j _ => measurable_pi_apply j

lemma T_eq (hM : Assumptions L M) (l : Fin (L + 1)) (s : ℝ) :
    T M l s = ∫ D, M.μ.real (Set.Ioi (s - Sl (l : ℕ) D)) ∂(P L M) := by
  haveI := hM.prob
  haveI := P_prob M hM
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (L + 1) => M.μ) (Fin.last L)
  set B : Set (ℝ × (Fin L → ℝ)) := {p | s < p.1 + Sl (l : ℕ) p.2} with hB
  have hBm : MeasurableSet B :=
    measurableSet_lt measurable_const (measurable_fst.add ((measurable_Sl _).comp measurable_snd))
  have hpre : {D : Fin (L + 1) → ℝ | s < ∑ j ∈ Finset.Ici l, D j} =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (L + 1) => ℝ) (Fin.last L)) ⁻¹' B := by
    ext D
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hB, sum_Ici_eq]
    simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
    exact Iff.rfl
  unfold T
  rw [hpre, hmp.measure_preimage hBm.nullMeasurableSet, Measure.prod_apply_symm hBm]
  have hfm : Measurable fun D : Fin L → ℝ => M.μ (Set.Ioi (s - Sl (l : ℕ) D)) := by
    have hanti : Antitone fun y : ℝ => M.μ (Set.Ioi y) := fun a b hab =>
      measure_mono (Set.Ioi_subset_Ioi hab)
    exact hanti.measurable.comp (measurable_const.sub (measurable_Sl _))
  have hset : ∀ D : Fin L → ℝ, (fun x => (x, D)) ⁻¹' B = Set.Ioi (s - Sl (l : ℕ) D) := by
    intro D; ext x; simp [hB]; constructor <;> intro h <;> linarith
  simp_rw [hset]
  rw [← integral_toReal hfm.aemeasurable (Filter.Eventually.of_forall fun _ => measure_lt_top _ _)]
  rfl

lemma integrable_tailS (hM : Assumptions L M) (l : ℕ) (s : ℝ) :
    Integrable (fun D => M.μ.real (Set.Ioi (s - Sl l D))) (P L M) := by
  haveI := hM.prob
  haveI := P_prob M hM
  refine Integrable.mono' (integrable_const 1) ?_ ?_
  · exact ((tail_anti M hM).measurable.comp
      (measurable_const.sub (measurable_Sl l))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun D => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one

lemma G_le_T (hM : Assumptions L M) (v : Fin L → ℝ) (l : Fin (L + 1)) (w : ℝ) :
    G M v w ≤ T M l (vext v l + w) := by
  rw [T_eq M hM]
  refine integral_mono (integrable_tail M hM v w) (integrable_tailS M hM _ _) fun D => ?_
  apply tail_anti M hM
  have := Y_ge hM.hL v D l (by have := l.isLt; omega)
  simp only [Sl]
  linarith

lemma T_anti (hM : Assumptions L M) (l : Fin (L + 1)) : Antitone (T M l) := by
  haveI := hM.prob
  intro a b hab
  unfold T
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun D hD => ?_)
  simp only [Set.mem_setOf_eq] at hD ⊢; linarith

lemma A_nonempty (hM : Assumptions L M) (l : Fin (L + 1)) :
    {s : ℝ | T M l s ≤ θbar M}.Nonempty := by
  haveI := hM.prob
  set ν := (Measure.pi fun _ : Fin (L + 1) => M.μ).map (fun D => ∑ j ∈ Finset.Ici l, D j)
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (measurable_sumIci l).aemeasurable
  obtain ⟨z, -, hz⟩ := tail_small ν (theta_pos M hM)
  refine ⟨z, ?_⟩
  show T M l z ≤ θbar M
  unfold T
  rw [show {D : Fin (L + 1) → ℝ | z < ∑ j ∈ Finset.Ici l, D j} =
    (fun D => ∑ j ∈ Finset.Ici l, D j) ⁻¹' Set.Ioi z from rfl,
    ← Measure.map_apply (measurable_sumIci l) measurableSet_Ioi]
  exact hz

lemma T_le_of_sbar_lt (hM : Assumptions L M) (l : Fin (L + 1)) (s : ℝ) (hs : sbar L M l < s) :
    T M l s ≤ θbar M := by
  obtain ⟨a, ha, has⟩ := exists_lt_of_csInf_lt (A_nonempty M hM l) hs
  exact (T_anti M hM l has.le).trans ha

lemma sbar_last_nonneg (hM : Assumptions L M) : 0 ≤ sbar L M (Fin.last L) := by
  haveI := hM.prob
  haveI := P_prob M hM
  refine le_csInf (A_nonempty M hM _) fun s hs => ?_
  by_contra hneg
  push_neg at hneg
  have hT : T M (Fin.last L) s = M.μ.real (Set.Ioi s) := by
    rw [T_eq M hM]
    have : ∀ D : Fin L → ℝ, Sl L D = 0 := by
      intro D; simp [Sl]
    simp [this]
  have h1 : M.μ.real (Set.Ici 0) ≤ M.μ.real (Set.Ioi s) :=
    measureReal_mono (Set.Ici_subset_Ioi.2 hneg)
  have h2 : M.μ.real (Set.Ici 0) = 1 := by
    rw [← Set.compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio, measureReal_def,
      hM.demand_nonneg]
    simp
  have h3 : T M (Fin.last L) s ≤ θbar M := hs
  have := theta_lt_one M hM
  linarith

lemma bound_of_pos (hM : Assumptions L M) (v : Fin L → ℝ) (zs : ℝ)
    (hbelow : ∀ w, 0 ≤ w → w < zs → θbar M < G M v w) (hz : 0 < zs) (l : Fin (L + 1)) :
    vext v l + zs ≤ sbar L M l := by
  by_contra hcon
  push_neg at hcon
  set w := (max 0 (sbar L M l - vext v l) + zs) / 2 with hw
  have hm1 := le_max_left 0 (sbar L M l - vext v l)
  have hm2 := le_max_right 0 (sbar L M l - vext v l)
  have hm3 : max 0 (sbar L M l - vext v l) < zs := max_lt hz (by linarith)
  have hw0 : 0 ≤ w := by linarith
  have hwz : w < zs := by linarith
  have h1 := hbelow w hw0 hwz
  have h2 := G_le_T M hM v l w
  have h3 := T_le_of_sbar_lt M hM l (vext v l + w) (by linarith)
  linarith

end Frac

end L6

open ZipkinLostSales.LNatural in
theorem lemma_6_core {L : ℕ} (M : Data) (hM : Assumptions L M) (v : Fin L → ℝ)
    (hv : v ∈ ZipkinLostSales.LNatural.V L) : ∃ z : ℝ, IsOptOrder M 0 v z ∧ InZ L M v z := by
  obtain ⟨zs, hleast, hbelow⟩ := L6.opt_exists M hM v
  have hg : ∀ z, gB M 0 v z = M.γ ^ L * L6.phi M v z := by
    intro z
    simp only [gB, gstep, fB, q, L6.phi, L6.P, MeasureTheory.integral_zero, mul_zero, add_zero]
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with D
    rw [L6.yPlusL_shift hM.hL]; rfl
  have hγ : 0 < M.γ ^ L := pow_pos hM.hγ0 L
  have hset : {z : ℝ | 0 ≤ z ∧ ∀ z' : ℝ, 0 ≤ z' → gB M 0 v z ≤ gB M 0 v z'} =
      {z | 0 ≤ z ∧ ∀ z', 0 ≤ z' → L6.phi M v z ≤ L6.phi M v z'} := by
    ext z
    simp only [Set.mem_setOf_eq, hg]
    constructor
    · rintro ⟨h0, h⟩; exact ⟨h0, fun z' hz' => le_of_mul_le_mul_left (h z' hz') hγ⟩
    · rintro ⟨h0, h⟩; exact ⟨h0, fun z' hz' => mul_le_mul_of_nonneg_left (h z' hz') hγ.le⟩
  have hvx : ∀ l : Fin L, vext v ((Fin.castSucc l : Fin (L + 1)) : ℕ) = v l := by
    intro l; simp [vext]
  have hvL : vext v ((Fin.last L : Fin (L + 1)) : ℕ) = 0 := by simp [vext]
  refine ⟨zs, ?_, ?_, ?_⟩
  · unfold IsOptOrder; rw [hset]; exact hleast
  · intro hnot
    by_contra hne
    have hpos : 0 < zs := lt_of_le_of_ne hleast.1.1 (Ne.symm hne)
    apply hnot
    refine ⟨hv, fun l => ?_⟩
    have := L6.bound_of_pos M hM v zs hbelow hpos l.castSucc
    rw [hvx] at this
    linarith
  · intro hin
    rcases eq_or_lt_of_le hleast.1.1 with h0 | hpos
    · rw [← h0]
      refine ⟨L6.sbar_last_nonneg M hM, fun l => ?_⟩
      simpa using hin.2 l
    · refine ⟨?_, fun l => ?_⟩
      · have := L6.bound_of_pos M hM v zs hbelow hpos (Fin.last L)
        rw [hvL] at this
        linarith
      · have := L6.bound_of_pos M hM v zs hbelow hpos l.castSucc
        rw [hvx] at this
        exact this

end ZipkinLostSales.Bounds

open ZipkinLostSales.Bounds


theorem solution {L : ℕ} (M : Data) (hM : Assumptions L M) (v : Fin L → ℝ) (hv : v ∈ ZipkinLostSales.LNatural.V L) :
    ∃ z : ℝ, IsOptOrder M 0 v z ∧ InZ L M v z := by
  exact lemma_6_core M hM v hv
