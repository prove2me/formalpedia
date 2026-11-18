-- Prove2me | solution 1 for OWMR.arb_indep_max
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T12:52:26.851292+00:00
-- url     : https://prove2.me/submissions/49b85834-6983-4fe3-a703-91009f5df744

import Definitions.Def_owmr_consolidation_policy
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
Lemma C.2 (independent-demand maximum), static form: for i.i.d. nonnegative integrable
`V_1, …, V_L` with law `ρ`, some `y ≥ 0` satisfies
`(h+p)(α y + 𝔼(V_max - y)⁺) ≤ (1 + h/p) NV_{h,p}(V_sum) + h 𝔼 V`, `α = h/(h+p)`.
The proof uses fractional threshold indicators in place of tie coins.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open OWMR

noncomputable section

namespace OWMR.L2aux

/-- Fractional threshold indicator `1{x > y} + θ 1{x = y}`. -/
def cw (y θ x : ℝ) : ℝ := if y < x then 1 else if x = y then θ else 0

lemma cw_nn {y θ : ℝ} (hθ : 0 ≤ θ) (x : ℝ) : 0 ≤ cw y θ x := by
  unfold cw; split_ifs <;> linarith

lemma cw_le {y θ : ℝ} (hθ : θ ≤ 1) (x : ℝ) : cw y θ x ≤ 1 := by
  unfold cw; split_ifs <;> linarith

lemma cw_meas (y θ : ℝ) : Measurable (cw y θ) := by
  unfold cw
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    (Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
      measurable_const)

lemma mul_cw (y θ x : ℝ) : x * cw y θ x = y * cw y θ x + max (x - y) 0 := by
  unfold cw
  split_ifs with h1 h2
  · rw [max_eq_left (by linarith)]; ring
  · rw [h2, max_eq_right (by linarith)]; ring
  · have : x < y := lt_of_le_of_ne (not_lt.1 h1) h2
    rw [max_eq_right (by linarith)]; ring

variable {K : ℕ}

/-- `V_max`. -/
def vmax (w : Fin (K + 1) → ℝ≥0) : ℝ := ((Finset.univ.sup w : ℝ≥0) : ℝ)

/-- The fractional union `1 - ∏ (1 - c(V_j))`. -/
def chi (y θ : ℝ) (w : Fin (K + 1) → ℝ≥0) : ℝ := 1 - ∏ j, (1 - cw y θ (w j))

lemma le_vmax (w : Fin (K + 1) → ℝ≥0) (j : Fin (K + 1)) : (w j : ℝ) ≤ vmax w :=
  NNReal.coe_le_coe.2 (Finset.le_sup (Finset.mem_univ j))

lemma vmax_eq (w : Fin (K + 1) → ℝ≥0) : ∃ j, vmax w = (w j : ℝ) := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty w
  exact ⟨j, by rw [vmax, hj]⟩

lemma vmax_nn (w : Fin (K + 1) → ℝ≥0) : 0 ≤ vmax w := NNReal.coe_nonneg _

lemma meas_fsup (s : Finset (Fin (K + 1))) :
    Measurable fun w : Fin (K + 1) → ℝ≥0 => s.sup w := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sup_empty]; exact measurable_const
  | insert j s hj ih =>
    simp only [Finset.sup_insert]
    exact (measurable_pi_apply j).sup ih

lemma vmax_meas : Measurable (vmax (K := K)) :=
  (meas_fsup Finset.univ).coe_nnreal_real

lemma prod_meas (y θ : ℝ) :
    Measurable fun w : Fin (K + 1) → ℝ≥0 => ∏ j, (1 - cw y θ (w j)) :=
  Finset.measurable_prod _ fun j _ =>
    measurable_const.sub ((cw_meas y θ).comp ((measurable_pi_apply j).coe_nnreal_real))

lemma chi_meas (y θ : ℝ) : Measurable (chi (K := K) y θ) :=
  measurable_const.sub (prod_meas y θ)

lemma prod_bounds {y θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (w : Fin (K + 1) → ℝ≥0) :
    0 ≤ ∏ j, (1 - cw y θ (w j)) ∧ ∏ j, (1 - cw y θ (w j)) ≤ 1 := by
  refine ⟨Finset.prod_nonneg fun j _ => by linarith [cw_le (y := y) hθ1 ((w j : ℝ))], ?_⟩
  exact Finset.prod_le_one (fun j _ => by linarith [cw_le (y := y) hθ1 ((w j : ℝ))])
    fun j _ => by linarith [cw_nn (y := y) hθ0 ((w j : ℝ))]

lemma chi_bounds {y θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (w : Fin (K + 1) → ℝ≥0) :
    0 ≤ chi y θ w ∧ chi y θ w ≤ 1 := by
  have := prod_bounds (y := y) hθ0 hθ1 w
  unfold chi; constructor <;> linarith [this.1, this.2]

/-- `V_max χ = y χ + (V_max - y)⁺`. -/
lemma vmax_chi {y θ : ℝ} (w : Fin (K + 1) → ℝ≥0) :
    vmax w * chi y θ w = y * chi y θ w + max (vmax w - y) 0 := by
  rcases lt_trichotomy y (vmax w) with hlt | heq | hgt
  · obtain ⟨j, hj⟩ := vmax_eq w
    have hc : cw y θ (w j) = 1 := by unfold cw; rw [if_pos (hj ▸ hlt)]
    have hp : ∏ l, (1 - cw y θ (w l)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hc]; ring)
    rw [chi, hp, max_eq_left (by linarith)]; ring
  · rw [← heq, max_eq_right (by linarith)]; ring
  · have hp : ∏ l, (1 - cw y θ (w l)) = 1 := by
      refine Finset.prod_eq_one fun l _ => ?_
      have h1 : (w l : ℝ) < y := lt_of_le_of_lt (le_vmax w l) hgt
      unfold cw; rw [if_neg (by linarith), if_neg (by linarith)]; ring
    rw [chi, hp, max_eq_right (by linarith)]; ring

lemma vmax_pos_part {y : ℝ} (w : Fin (K + 1) → ℝ≥0) :
    max (vmax w - y) 0 ≤ ∑ j, max ((w j : ℝ) - y) 0 := by
  obtain ⟨j, hj⟩ := vmax_eq w
  rw [hj]
  exact Finset.single_le_sum (f := fun j => max ((w j : ℝ) - y) 0)
    (fun l _ => le_max_right _ _) (Finset.mem_univ j)

variable (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]

omit [IsProbabilityMeasure ρ] in
lemma int_coe (hρ : ∫⁻ x, (x : ℝ≥0∞) ∂ρ < ∞) : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ := by
  have h1 := integrable_toReal_of_lintegral_ne_top (μ := ρ) (f := fun x : ℝ≥0 => (x : ℝ≥0∞))
    measurable_coe_nnreal_ennreal.aemeasurable hρ.ne
  simpa using h1

lemma int_coord (hρ : ∫⁻ x, (x : ℝ≥0∞) ∂ρ < ∞) (j : Fin (K + 1)) :
    Integrable (fun w : Fin (K + 1) → ℝ≥0 => (w j : ℝ)) (Measure.pi fun _ : Fin (K + 1) => ρ) := by
  have hmp := measurePreserving_eval (μ := fun _ : Fin (K + 1) => ρ) j
  exact (hmp.integrable_comp measurable_coe_nnreal_real.aestronglyMeasurable).2 (int_coe ρ hρ)

lemma int_coord_eq (j : Fin (K + 1)) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ w : Fin (K + 1) → ℝ≥0, f (w j) ∂(Measure.pi fun _ : Fin (K + 1) => ρ) = ∫ x, f x ∂ρ := by
  have hmp := measurePreserving_eval (μ := fun _ : Fin (K + 1) => ρ) j
  have h1 := integral_map (μ := Measure.pi fun _ : Fin (K + 1) => ρ) (φ := Function.eval j)
    (f := fun x : ℝ≥0 => f (x : ℝ)) (measurable_pi_apply j).aemeasurable
    (hf.comp measurable_coe_nnreal_real).aestronglyMeasurable
  rw [hmp.map_eq] at h1
  exact h1.symm

lemma int_sum (hρ : ∫⁻ x, (x : ℝ≥0∞) ∂ρ < ∞) :
    Integrable (fun w : Fin (K + 1) → ℝ≥0 => ∑ j, (w j : ℝ)) (Measure.pi fun _ : Fin (K + 1) => ρ) :=
  integrable_finsetSum _ fun j _ => int_coord ρ hρ j

lemma int_vmax (hρ : ∫⁻ x, (x : ℝ≥0∞) ∂ρ < ∞) :
    Integrable (vmax (K := K)) (Measure.pi fun _ : Fin (K + 1) => ρ) := by
  refine (int_sum ρ hρ).mono' vmax_meas.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (vmax_nn w)]
  obtain ⟨j, hj⟩ := vmax_eq w
  rw [hj]
  exact Finset.single_le_sum (f := fun j => (w j : ℝ)) (fun l _ => NNReal.coe_nonneg _)
    (Finset.mem_univ j)

lemma sum_mean (hρ : ∫⁻ x, (x : ℝ≥0∞) ∂ρ < ∞) :
    ∫ w : Fin (K + 1) → ℝ≥0, ∑ j, (w j : ℝ) ∂(Measure.pi fun _ : Fin (K + 1) => ρ)
      = (K + 1) * ∫ x, (x : ℝ) ∂ρ := by
  rw [integral_finsetSum _ fun j _ => int_coord ρ hρ j]
  have hj : ∀ j : Fin (K + 1), ∫ w : Fin (K + 1) → ℝ≥0, (w j : ℝ) ∂(Measure.pi fun _ : Fin (K + 1) => ρ)
      = ∫ x, (x : ℝ) ∂ρ := fun j => int_coord_eq ρ j (fun x => x) measurable_id
  simp only [hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

lemma whLoss_abs_le (h p y : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) : |whLoss h p y| ≤ (h + p) * |y| := by
  unfold whLoss
  have h1 : 0 ≤ h * max y 0 + p * max (-y) 0 := by positivity
  rw [abs_of_nonneg h1]
  have a1 : max y 0 ≤ |y| := max_le (le_abs_self y) (abs_nonneg y)
  have a2 : max (-y) 0 ≤ |y| := max_le (neg_le_abs y) (abs_nonneg y)
  have b1 : h * max y 0 ≤ h * |y| := mul_le_mul_of_nonneg_left a1 hh
  have b2 : p * max (-y) 0 ≤ p * |y| := mul_le_mul_of_nonneg_left a2 hp
  nlinarith

lemma whLoss_cont (h p : ℝ) : Continuous (whLoss h p) := by
  unfold whLoss; fun_prop

lemma int_whLoss {α : Type*} [MeasurableSpace α] {μ : Measure α} (h p : ℝ) (hh : 0 ≤ h)
    (hp : 0 ≤ p) {g : α → ℝ} (hg : Integrable g μ) :
    Integrable (fun x => whLoss h p (g x)) μ := by
  refine Integrable.mono' (hg.norm.const_mul (h + p))
    ((whLoss_cont h p).comp_aestronglyMeasurable hg.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using whLoss_abs_le h p (g x) hh hp

/-- The weighted bound: `h 𝔼[(V_sum - 𝔼 V_sum) w] ≤ 𝔼 φ(z - V_sum)` for weights in `[0, 1/α]`
with mean one. -/
lemma weighted (hρ : ∫⁻ x, (x : ℝ≥0∞) ∂ρ < ∞) (h p : ℝ) (hh : 0 < h) (hp : 0 < p)
    (wt : (Fin (K + 1) → ℝ≥0) → ℝ) (hwm : Measurable wt) (hw0 : ∀ w, 0 ≤ wt w)
    (hw1 : ∀ w, h * wt w ≤ h + p) (hwE : ∫ w, wt w ∂(Measure.pi fun _ : Fin (K + 1) => ρ) = 1) (z : ℝ) :
    h * ∫ w, (∑ j, (w j : ℝ) - (K + 1) * ∫ x, (x : ℝ) ∂ρ) * wt w ∂(Measure.pi fun _ : Fin (K + 1) => ρ)
      ≤ ∫ w, whLoss h p (z - ∑ j, (w j : ℝ)) ∂(Measure.pi fun _ : Fin (K + 1) => ρ) := by
  set μL := Measure.pi fun _ : Fin (K + 1) => ρ
  set m := ∫ x, (x : ℝ) ∂ρ
  set S : (Fin (K + 1) → ℝ≥0) → ℝ := fun w => ∑ j, (w j : ℝ)
  have hSi : Integrable S μL := int_sum ρ hρ
  have hwb : ∀ w, ‖wt w‖ ≤ (h + p) / h := fun w => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 w), le_div_iff₀ hh]; linarith [hw1 w]
  have hi1 : Integrable (fun w => (S w - (K + 1) * m) * wt w) μL :=
    (hSi.sub (integrable_const _)).mul_bdd hwm.aestronglyMeasurable
      (Eventually.of_forall hwb)
  have hpos : Integrable (fun w => max (S w - z) 0) μL :=
    (hSi.sub (integrable_const z)).pos_part
  have hi2 : Integrable (fun w => h * max (S w - z) 0 * wt w + h * (z - (K + 1) * m) * wt w) μL :=
    ((hpos.const_mul h).mul_bdd hwm.aestronglyMeasurable (Eventually.of_forall hwb)).add
      ((integrable_const _).mul_bdd hwm.aestronglyMeasurable (Eventually.of_forall hwb))
  have hg : Integrable (fun w => z - S w) μL := (integrable_const z).sub hSi
  have hi3 : Integrable (fun w => whLoss h p (z - S w)) μL := int_whLoss h p hh.le hp.le hg
  have hpt : ∀ w, h * ((S w - (K + 1) * m) * wt w)
      ≤ h * max (S w - z) 0 * wt w + h * (z - (K + 1) * m) * wt w := by
    intro w
    have e : h * ((S w - (K + 1) * m) * wt w)
        = h * (S w - z) * wt w + h * (z - (K + 1) * m) * wt w := by ring
    rw [e]
    have : h * (S w - z) ≤ h * max (S w - z) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hh.le
    nlinarith [hw0 w]
  have hpt2 : ∀ w, h * max (S w - z) 0 * wt w ≤ (h + p) * max (S w - z) 0 := by
    intro w
    have := le_max_right (S w - z) 0
    nlinarith [hw1 w, hw0 w]
  have hloss : ∀ w, whLoss h p (z - S w) = h * (z - S w) + (h + p) * max (S w - z) 0 := by
    intro w
    unfold whLoss
    rcases le_total (S w) z with hle | hle
    · rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
      ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]
      ring
  have hval : ∫ w, whLoss h p (z - S w) ∂μL
      = h * (z - (K + 1) * m) + (h + p) * ∫ w, max (S w - z) 0 ∂μL := by
    calc ∫ w, whLoss h p (z - S w) ∂μL
        = ∫ w, (h * (z - S w) + (h + p) * max (S w - z) 0) ∂μL :=
          integral_congr_ae (Eventually.of_forall hloss)
      _ = h * ∫ w, (z - S w) ∂μL + (h + p) * ∫ w, max (S w - z) 0 ∂μL := by
          rw [integral_add (hg.const_mul h) (hpos.const_mul _), integral_const_mul,
            integral_const_mul]
      _ = h * (z - (K + 1) * m) + (h + p) * ∫ w, max (S w - z) 0 ∂μL := by
          have hz : ∫ _w, z ∂μL = z := by simp [μL]
          rw [integral_sub (integrable_const z) hSi, sum_mean ρ hρ, hz]
  have hA : Integrable (fun w => h * max (S w - z) 0 * wt w) μL :=
    (hpos.const_mul h).mul_bdd hwm.aestronglyMeasurable (Eventually.of_forall hwb)
  have hB : Integrable (fun w => h * (z - (K + 1) * m) * wt w) μL :=
    (integrable_const _).mul_bdd hwm.aestronglyMeasurable (Eventually.of_forall hwb)
  calc h * ∫ w, (S w - (K + 1) * m) * wt w ∂μL
      = ∫ w, h * ((S w - (K + 1) * m) * wt w) ∂μL := (integral_const_mul _ _).symm
    _ ≤ ∫ w, (h * max (S w - z) 0 * wt w + h * (z - (K + 1) * m) * wt w) ∂μL :=
        integral_mono (hi1.const_mul h) hi2 hpt
    _ = ∫ w, h * max (S w - z) 0 * wt w ∂μL + h * (z - (K + 1) * m) := by
        rw [integral_add hA hB, integral_const_mul, hwE, mul_one]
    _ ≤ ∫ w, (h + p) * max (S w - z) 0 ∂μL + h * (z - (K + 1) * m) :=
        add_le_add (integral_mono hA (hpos.const_mul _) hpt2) le_rfl
    _ = ∫ w, whLoss h p (z - S w) ∂μL := by
        rw [hval, integral_const_mul]; ring

/-- Expected value of the product: `𝔼 ∏ (1 - c(V_j)) = (1 - r)^(K+1)`. -/
lemma int_prod {y θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∫ w : Fin (K + 1) → ℝ≥0, ∏ j, (1 - cw y θ (w j)) ∂(Measure.pi fun _ : Fin (K + 1) => ρ)
      = (1 - ∫ x, cw y θ x ∂ρ) ^ (K + 1) := by
  rw [integral_fintype_prod_eq_pow (f := fun x : ℝ≥0 => 1 - cw y θ x), Fintype.card_fin]
  congr 1
  rw [integral_sub (integrable_const 1) ?_]
  · simp
  · refine Integrable.mono' (integrable_const (1 : ℝ))
      ((cw_meas y θ).comp measurable_coe_nnreal_real).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [cw_nn (y := y) hθ0 (x : ℝ)], cw_le (y := y) hθ1 (x : ℝ)⟩

/-- `1 - ∏`: integral of the fractional union. -/
lemma int_chi {y θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∫ w, chi y θ w ∂(Measure.pi fun _ : Fin (K + 1) => ρ) = 1 - (1 - ∫ x, cw y θ x ∂ρ) ^ (K + 1) := by
  have hi : Integrable (fun w : Fin (K + 1) → ℝ≥0 => ∏ j, (1 - cw y θ (w j)))
      (Measure.pi fun _ : Fin (K + 1) => ρ) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) (prod_meas y θ).aestronglyMeasurable
      (Eventually.of_forall fun w => ?_)
    have := prod_bounds (y := y) hθ0 hθ1 w
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  unfold chi
  rw [integral_sub (integrable_const 1) hi, int_prod ρ hθ0 hθ1]
  simp

lemma chi_int {y θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Integrable (chi (K := K) y θ) (Measure.pi fun _ : Fin (K + 1) => ρ) := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) (chi_meas y θ).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  have := chi_bounds (y := y) hθ0 hθ1 w
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]

lemma chi_norm {y θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (w : Fin (K + 1) → ℝ≥0) :
    ‖chi y θ w‖ ≤ 1 := by
  have := chi_bounds (y := y) hθ0 hθ1 w
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]

lemma cw_int {y θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Integrable (fun x : ℝ≥0 => cw y θ x) ρ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    ((cw_meas y θ).comp measurable_coe_nnreal_real).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [cw_nn (y := y) hθ0 (x : ℝ)], cw_le (y := y) hθ1 (x : ℝ)⟩

/-- `𝔼[V_j χ] = m - (m - 𝔼[V c(V)]) (1 - r)^K`. -/
lemma int_coord_chi (hρ : ∫⁻ x, (x : ℝ≥0∞) ∂ρ < ∞) {y θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (j : Fin (K + 1)) :
    ∫ w, (w j : ℝ) * chi y θ w ∂(Measure.pi fun _ : Fin (K + 1) => ρ)
      = ∫ x, (x : ℝ) ∂ρ - (∫ x, (x : ℝ) ∂ρ - ∫ x, (x : ℝ) * cw y θ x ∂ρ)
          * (1 - ∫ x, cw y θ x ∂ρ) ^ K := by
  set μL := Measure.pi fun _ : Fin (K + 1) => ρ
  set f : Fin (K + 1) → ℝ≥0 → ℝ := fun l x => (if l = j then (x : ℝ) else 1) * (1 - cw y θ x)
  have hprod : ∀ w : Fin (K + 1) → ℝ≥0,
      ∏ l, f l (w l) = (w j : ℝ) * ∏ l, (1 - cw y θ (w l)) := by
    intro w
    simp only [f, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq' Finset.univ j (fun l => (w l : ℝ))]
    simp
  have hfi : ∀ l, Integrable (f l) ρ := by
    intro l
    by_cases hl : l = j
    · simp only [f, if_pos hl]
      refine Integrable.mono' (int_coe ρ hρ)
        ((measurable_coe_nnreal_real.mul (measurable_const.sub
          ((cw_meas y θ).comp measurable_coe_nnreal_real))).aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (NNReal.coe_nonneg x)]
      have h1 : |1 - cw y θ x| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [cw_nn (y := y) hθ0 (x : ℝ), cw_le (y := y) hθ1 (x : ℝ)]
      nlinarith [NNReal.coe_nonneg x, abs_nonneg (1 - cw y θ x)]
    · simp only [f, if_neg hl, one_mul]
      exact (integrable_const 1).sub (cw_int ρ hθ0 hθ1)
  have hfv : ∀ l, ∫ x, f l x ∂ρ
      = if l = j then ∫ x, (x : ℝ) ∂ρ - ∫ x, (x : ℝ) * cw y θ x ∂ρ
        else 1 - ∫ x, cw y θ x ∂ρ := by
    intro l
    by_cases hl : l = j
    · simp only [f, if_pos hl]
      have hxc : Integrable (fun x : ℝ≥0 => (x : ℝ) * cw y θ x) ρ :=
        (int_coe ρ hρ).mul_bdd (c := 1) ((cw_meas y θ).comp measurable_coe_nnreal_real).aestronglyMeasurable
          (Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_le]
            exact ⟨by linarith [cw_nn (y := y) hθ0 (x : ℝ)], cw_le (y := y) hθ1 (x : ℝ)⟩)
      have e : (fun x : ℝ≥0 => (x : ℝ) * (1 - cw y θ x)) = fun x : ℝ≥0 => (x : ℝ) - (x : ℝ) * cw y θ x := by
        funext x; ring
      rw [e, integral_sub (int_coe ρ hρ) hxc]
    · simp only [f, if_neg hl, one_mul]
      rw [integral_sub (integrable_const 1) (cw_int ρ hθ0 hθ1)]
      simp
  have hint : ∫ w, ∏ l, f l (w l) ∂μL
      = (∫ x, (x : ℝ) ∂ρ - ∫ x, (x : ℝ) * cw y θ x ∂ρ) * (1 - ∫ x, cw y θ x ∂ρ) ^ K := by
    rw [integral_fintype_prod_eq_prod (f := f)]
    simp only [hfv]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), if_pos rfl]
    congr 1
    rw [Finset.prod_congr rfl (fun l hl => if_neg (Finset.ne_of_mem_erase hl)),
      Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j)]
    simp
  have hci : Integrable (fun w : Fin (K + 1) → ℝ≥0 => (w j : ℝ)) μL := int_coord ρ hρ j
  have hpi : Integrable (fun w : Fin (K + 1) → ℝ≥0 => (w j : ℝ) * ∏ l, (1 - cw y θ (w l))) μL := by
    refine hci.mul_bdd (c := 1) (prod_meas y θ).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    have := prod_bounds (y := y) hθ0 hθ1 w
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  have e2 : (fun w : Fin (K + 1) → ℝ≥0 => (w j : ℝ) * chi y θ w)
      = fun w => (w j : ℝ) - (w j : ℝ) * ∏ l, (1 - cw y θ (w l)) := by
    funext w; unfold chi; ring
  rw [e2, integral_sub hci hpi, int_coord_eq ρ j (fun x => x) measurable_id]
  simp only [← hprod]
  rw [hint]

/-- The covariance inequality `Cov(V_sum, χ) ≥ (1 - q) 𝔼[(V_max - m) χ]` for `y ≥ m`. -/
lemma cov_ineq (hρ : ∫⁻ x, (x : ℝ≥0∞) ∂ρ < ∞) {y θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hym : ∫ x, (x : ℝ) ∂ρ ≤ y) :
    (1 - ∫ x, cw y θ x ∂ρ) ^ (K + 1)
        * ∫ w, (vmax w - ∫ x, (x : ℝ) ∂ρ) * chi y θ w ∂(Measure.pi fun _ : Fin (K + 1) => ρ)
      ≤ ∫ w, (∑ j, (w j : ℝ) - (K + 1) * ∫ x, (x : ℝ) ∂ρ) * chi y θ w
          ∂(Measure.pi fun _ : Fin (K + 1) => ρ) := by
  set μL := Measure.pi fun _ : Fin (K + 1) => ρ
  set m := ∫ x, (x : ℝ) ∂ρ with hm
  set r := ∫ x, cw y θ x ∂ρ with hr
  set E := ∫ x, max ((x : ℝ) - y) 0 ∂ρ with hE
  have hr0 : 0 ≤ r := integral_nonneg fun x => cw_nn (y := y) hθ0 (x : ℝ)
  have hr1 : r ≤ 1 := by
    have : r ≤ ∫ _x, (1 : ℝ) ∂ρ :=
      integral_mono (cw_int ρ hθ0 hθ1) (integrable_const 1) fun x => cw_le (y := y) hθ1 (x : ℝ)
    simpa using this
  have hm0 : 0 ≤ m := integral_nonneg fun x => NNReal.coe_nonneg x
  have hE0 : 0 ≤ E := integral_nonneg fun x => le_max_right _ _
  have hposi : Integrable (fun x : ℝ≥0 => max ((x : ℝ) - y) 0) ρ :=
    ((int_coe ρ hρ).sub (integrable_const y)).pos_part
  -- 𝔼[V c(V)] = y r + E
  have hxc : ∫ x, (x : ℝ) * cw y θ x ∂ρ = y * r + E := by
    have e : (fun x : ℝ≥0 => (x : ℝ) * cw y θ x) = fun x : ℝ≥0 => y * cw y θ x + max ((x : ℝ) - y) 0 := by
      funext x; exact mul_cw y θ x
    rw [e, integral_add ((cw_int ρ hθ0 hθ1).const_mul y) hposi, integral_const_mul]
  have hchi_i := chi_int (K := K) (y := y) ρ hθ0 hθ1
  have hSi := int_sum (K := K) ρ hρ
  -- the covariance
  have hcov : ∫ w, (∑ j, (w j : ℝ) - (K + 1) * m) * chi y θ w ∂μL
      = (K + 1) * (1 - r) ^ K * ((y - m) * r + E) := by
    have e : (fun w : Fin (K + 1) → ℝ≥0 => (∑ j, (w j : ℝ) - (K + 1) * m) * chi y θ w)
        = fun w => ∑ j, (w j : ℝ) * chi y θ w - (K + 1) * m * chi y θ w := by
      funext w; rw [sub_mul, Finset.sum_mul]
    have hji : ∀ j : Fin (K + 1), Integrable (fun w : Fin (K + 1) → ℝ≥0 => (w j : ℝ) * chi y θ w) μL :=
      fun j => (int_coord ρ hρ j).mul_bdd (c := 1) (chi_meas y θ).aestronglyMeasurable
        (Eventually.of_forall (chi_norm hθ0 hθ1))
    have hsum : ∫ w, ∑ j, (w j : ℝ) * chi y θ w ∂μL
        = (K + 1) * (m - (m - (y * r + E)) * (1 - r) ^ K) := by
      rw [integral_finsetSum _ fun j _ => hji j]
      rw [Finset.sum_congr rfl (fun j _ => int_coord_chi ρ hρ hθ0 hθ1 j)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hxc]
      push_cast; ring
    rw [e, integral_sub (integrable_finsetSum _ fun j _ => hji j) (hchi_i.const_mul _),
      hsum, integral_const_mul, int_chi ρ hθ0 hθ1]
    ring
  -- 𝔼[(V_max - m) χ] = (y - m) q + 𝔼(V_max - y)⁺
  have hvi : Integrable (vmax (K := K)) μL := int_vmax ρ hρ
  have hvposi : Integrable (fun w : Fin (K + 1) → ℝ≥0 => max (vmax w - y) 0) μL :=
    (hvi.sub (integrable_const y)).pos_part
  have hvc : ∫ w, (vmax w - m) * chi y θ w ∂μL
      = (y - m) * (1 - (1 - r) ^ (K + 1)) + ∫ w, max (vmax w - y) 0 ∂μL := by
    have e : (fun w : Fin (K + 1) → ℝ≥0 => (vmax w - m) * chi y θ w)
        = fun w => (y - m) * chi y θ w + max (vmax w - y) 0 := by
      funext w
      have := vmax_chi (y := y) (θ := θ) w
      linear_combination this
    rw [e, integral_add (hchi_i.const_mul _) hvposi, integral_const_mul, int_chi ρ hθ0 hθ1]
  -- 𝔼(V_max - y)⁺ ≤ (K + 1) E
  have hvE : ∫ w, max (vmax w - y) 0 ∂μL ≤ (K + 1) * E := by
    have hji2 : ∀ j : Fin (K + 1),
        Integrable (fun w : Fin (K + 1) → ℝ≥0 => max ((w j : ℝ) - y) 0) μL :=
      fun j => ((int_coord ρ hρ j).sub (integrable_const y)).pos_part
    have hsi : Integrable (fun w : Fin (K + 1) → ℝ≥0 => ∑ j, max ((w j : ℝ) - y) 0) μL :=
      integrable_finsetSum _ fun j _ => hji2 j
    calc ∫ w, max (vmax w - y) 0 ∂μL ≤ ∫ w, ∑ j, max ((w j : ℝ) - y) 0 ∂μL :=
          integral_mono hvposi hsi fun w => vmax_pos_part w
      _ = (K + 1) * E := by
          rw [integral_finsetSum _ fun j _ => hji2 j]
          have hj : ∀ j : Fin (K + 1), ∫ w : Fin (K + 1) → ℝ≥0, max ((w j : ℝ) - y) 0 ∂μL = E :=
            fun j => int_coord_eq ρ j (fun x => max (x - y) 0) (by fun_prop)
          rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  rw [hcov, hvc]
  -- algebra
  have hq : 1 - (1 - r) ^ (K + 1) ≤ (K + 1) * r := by
    have := one_add_mul_le_pow (a := -r) (by linarith) (K + 1)
    rw [← sub_eq_add_neg] at this
    push_cast at this; linarith
  have hpw : (1 - r) ^ (K + 1) ≤ (1 - r) ^ K := by
    rw [pow_succ]; exact mul_le_of_le_one_right (pow_nonneg (by linarith) _) (by linarith)
  have hpw0 : 0 ≤ (1 - r) ^ (K + 1) := pow_nonneg (by linarith) _
  have hym' : 0 ≤ y - m := by linarith
  have hb : 0 ≤ (y - m) * r + E := by positivity
  calc (1 - r) ^ (K + 1) * ((y - m) * (1 - (1 - r) ^ (K + 1)) + ∫ w, max (vmax w - y) 0 ∂μL)
      ≤ (1 - r) ^ (K + 1) * ((K + 1) * ((y - m) * r + E)) := by
        apply mul_le_mul_of_nonneg_left _ hpw0
        nlinarith [mul_le_mul_of_nonneg_left hq hym']
    _ ≤ (1 - r) ^ K * ((K + 1) * ((y - m) * r + E)) :=
        mul_le_mul_of_nonneg_right hpw (by positivity)
    _ = (K + 1) * (1 - r) ^ K * ((y - m) * r + E) := by ring

lemma vc_eq (hρ : ∫⁻ x, (x : ℝ≥0∞) ∂ρ < ∞) {y θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (m : ℝ) :
    ∫ w, (vmax w - m) * chi y θ w ∂(Measure.pi fun _ : Fin (K + 1) => ρ)
      = (y - m) * (1 - (1 - ∫ x, cw y θ x ∂ρ) ^ (K + 1))
        + ∫ w, max (vmax w - y) 0 ∂(Measure.pi fun _ : Fin (K + 1) => ρ) := by
  have hchi_i := chi_int (K := K) (y := y) ρ hθ0 hθ1
  have hvposi : Integrable (fun w : Fin (K + 1) → ℝ≥0 => max (vmax w - y) 0)
      (Measure.pi fun _ : Fin (K + 1) => ρ) :=
    ((int_vmax ρ hρ).sub (integrable_const y)).pos_part
  have e : (fun w : Fin (K + 1) → ℝ≥0 => (vmax w - m) * chi y θ w)
      = fun w => (y - m) * chi y θ w + max (vmax w - y) 0 := by
    funext w
    have := vmax_chi (y := y) (θ := θ) w
    linear_combination this
  rw [e, integral_add (hchi_i.const_mul _) hvposi, integral_const_mul, int_chi ρ hθ0 hθ1]

/-- An upper quantile of `ρ` at level `r ∈ (0,1)`. -/
lemma quantile (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ y : ℝ, 0 ≤ y ∧ ρ.real {x : ℝ≥0 | y < (x : ℝ)} ≤ r ∧ r ≤ ρ.real {x : ℝ≥0 | y ≤ (x : ℝ)} := by
  set G : ℝ → ℝ := fun t => ρ.real {x : ℝ≥0 | t < (x : ℝ)} with hG
  have hGanti : Antitone G := fun a b hab =>
    measureReal_mono (fun x (hx : b < (x : ℝ)) => (lt_of_le_of_lt hab hx : a < (x : ℝ)))
  have hGneg : ∀ t < 0, G t = 1 := by
    intro t ht
    have : {x : ℝ≥0 | t < (x : ℝ)} = univ := eq_univ_of_forall fun x => lt_of_lt_of_le ht x.2
    simp only [hG, this, probReal_univ]
  have hmeas : ∀ t : ℝ, MeasurableSet {x : ℝ≥0 | t < (x : ℝ)} := fun t =>
    measurableSet_lt measurable_const measurable_coe_nnreal_real
  have hlim : Tendsto (fun k : ℕ => G k) atTop (𝓝 0) := by
    have h1 := tendsto_measure_iInter_atTop (μ := ρ)
      (s := fun k : ℕ => {x : ℝ≥0 | (k : ℝ) < (x : ℝ)})
      (fun k => (hmeas k).nullMeasurableSet)
      (fun a b hab x (hx : ((b : ℕ) : ℝ) < (x : ℝ)) =>
        (lt_of_le_of_lt (Nat.cast_le.2 hab) hx : ((a : ℕ) : ℝ) < (x : ℝ)))
      ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ k : ℕ, {x : ℝ≥0 | (k : ℝ) < (x : ℝ)}) = ∅ := by
      ext x
      simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
      exact ⟨⌈(x : ℝ)⌉₊, Nat.le_ceil _⟩
    rw [hempty, measure_empty] at h1
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [hG, Measure.real, Function.comp_def] using h2
  obtain ⟨k0, hk0⟩ := (hlim.eventually (gt_mem_nhds hr0)).exists
  set A : Set ℝ := {t | G t ≤ r} with hA
  have hAne : A.Nonempty := ⟨k0, hk0.le⟩
  have hAlow : ∀ t ∈ A, 0 ≤ t := by
    intro t ht
    by_contra hneg
    rw [not_le] at hneg
    have h1 : G t = 1 := hGneg t hneg
    have h2 : G t ≤ r := ht
    linarith
  have hAbdd : BddBelow A := ⟨0, hAlow⟩
  set y := sInf A with hy
  have hy0 : 0 ≤ y := le_csInf hAne hAlow
  refine ⟨y, hy0, ?_, ?_⟩
  · have hmono : Monotone fun k : ℕ => {x : ℝ≥0 | y + 1 / ((k : ℝ) + 1) < (x : ℝ)} := by
      intro a b hab x hx
      simp only [mem_ofPred_eq] at hx ⊢
      have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
      linarith
    have hU : (⋃ k : ℕ, {x : ℝ≥0 | y + 1 / ((k : ℝ) + 1) < (x : ℝ)})
        = {x : ℝ≥0 | y < (x : ℝ)} := by
      ext x
      simp only [mem_iUnion, mem_ofPred_eq]
      constructor
      · rintro ⟨k, hk⟩
        have : 0 < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      · intro hx
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
        exact ⟨k, by linarith⟩
    have h1 := tendsto_measure_iUnion_atTop (μ := ρ) hmono
    rw [hU] at h1
    have h2 := (ENNReal.tendsto_toReal (measure_ne_top ρ _)).comp h1
    have hle : ∀ k : ℕ, G (y + 1 / ((k : ℝ) + 1)) ≤ r := by
      intro k
      have hlt : sInf A < y + 1 / ((k : ℝ) + 1) := by
        rw [← hy]; have : 0 < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      obtain ⟨a, haA, hay⟩ := exists_lt_of_csInf_lt hAne hlt
      exact (hGanti hay.le).trans haA
    exact le_of_tendsto' h2 fun k => hle k
  · have hanti : Antitone fun k : ℕ => {x : ℝ≥0 | y - 1 / ((k : ℝ) + 1) < (x : ℝ)} := by
      intro a b hab x hx
      simp only [mem_ofPred_eq] at hx ⊢
      have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
      linarith
    have hI : (⋂ k : ℕ, {x : ℝ≥0 | y - 1 / ((k : ℝ) + 1) < (x : ℝ)})
        = {x : ℝ≥0 | y ≤ (x : ℝ)} := by
      ext x
      simp only [mem_iInter, mem_ofPred_eq]
      constructor
      · intro hx
        by_contra hlt
        rw [not_le] at hlt
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
        have := hx k
        linarith
      · intro hx k
        have : 0 < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    have h1 := tendsto_measure_iInter_atTop (μ := ρ) (fun k => (hmeas _).nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    rw [hI] at h1
    have h2 := (ENNReal.tendsto_toReal (measure_ne_top ρ _)).comp h1
    have hge : ∀ k : ℕ, r ≤ G (y - 1 / ((k : ℝ) + 1)) := by
      intro k
      have hlt : y - 1 / ((k : ℝ) + 1) < sInf A := by
        rw [← hy]; have : 0 < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      have := notMem_of_lt_csInf hlt hAbdd
      simp only [hA, mem_ofPred_eq, not_le] at this
      exact this.le
    exact ge_of_tendsto' h2 fun k => hge k

lemma cw_zero (y x : ℝ) : cw y 0 x = {t : ℝ | y < t}.indicator 1 x := by
  unfold cw
  by_cases h : y < x
  · simp [h]
  · simp [h]

lemma cw_one (y x : ℝ) : cw y 1 x = {t : ℝ | y ≤ t}.indicator 1 x := by
  unfold cw
  by_cases h : y < x
  · simp [h, h.le]
  · by_cases h2 : x = y
    · simp [h2]
    · have : ¬ y ≤ x := fun hle => h (lt_of_le_of_ne hle (Ne.symm h2))
      simp [h, h2, this]

lemma cw_affine (y θ x : ℝ) : cw y θ x = cw y 0 x + θ * (if x = y then 1 else 0) := by
  unfold cw
  by_cases h1 : y < x
  · have h2 : x ≠ y := ne_of_gt h1
    simp [h1, h2]
  · by_cases h2 : x = y <;> simp [h1, h2]

end OWMR.L2aux

end

open OWMR.L2aux in
theorem solution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : ∫⁻ x, (x : ℝ≥0∞) ∂ρ < ∞)
    (L : ℕ) (h p : ℝ) (hh : 0 < h) (hp : 0 < p) :
    ∃ y : ℝ, 0 ≤ y ∧
      (h + p) * (h / (h + p) * y
          + ∫ w, max (((Finset.univ.sup w : ℝ≥0) : ℝ) - y) 0 ∂(Measure.pi fun _ : Fin L => ρ))
        ≤ (1 + h / p) * (⨅ z : ℝ, ∫ w, whLoss h p (z - ∑ j, (w j : ℝ))
            ∂(Measure.pi fun _ : Fin L => ρ))
          + h * ∫ x, (x : ℝ) ∂ρ := by
  have hm0 : 0 ≤ ∫ x, (x : ℝ) ∂ρ := integral_nonneg fun x => NNReal.coe_nonneg x
  have hNV0 : ∀ L : ℕ, 0 ≤ ⨅ z : ℝ, ∫ w, whLoss h p (z - ∑ j, (w j : ℝ))
      ∂(Measure.pi fun _ : Fin L => ρ) := fun L =>
    le_ciInf fun z => integral_nonneg fun w => by unfold whLoss; positivity
  have hhp : 0 < h + p := by linarith
  cases L with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    have e : ∀ w : Fin 0 → ℝ≥0, max (((Finset.univ.sup w : ℝ≥0) : ℝ) - 0) 0 = 0 := fun w => by
      simp
    simp only [e, integral_zero, mul_zero, add_zero]
    exact add_nonneg (mul_nonneg (by positivity) (hNV0 0)) (mul_nonneg hh.le hm0)
  | succ K =>
    set μL := Measure.pi fun _ : Fin (K + 1) => ρ with hμL
    set m := ∫ x, (x : ℝ) ∂ρ with hm
    set NV := ⨅ z : ℝ, ∫ w, whLoss h p (z - ∑ j, (w j : ℝ)) ∂μL with hNV
    set α := h / (h + p) with hα
    have hα0 : 0 < α := div_pos hh hhp
    have hα1 : α < 1 := (div_lt_one hhp).2 (by linarith)
    have hαh : (h + p) * α = h := by rw [hα]; field_simp
    have hαp : (h + p) * (1 - α) = p := by rw [mul_sub, hαh]; ring
    have hS := int_sum (K := K) ρ hρ
    have hSm : Measurable fun w : Fin (K + 1) → ℝ≥0 => ∑ j, (w j : ℝ) :=
      Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real
    -- the weighted bound against the newsvendor value
    have hwNV : ∀ wt : (Fin (K + 1) → ℝ≥0) → ℝ, Measurable wt → (∀ w, 0 ≤ wt w) →
        (∀ w, h * wt w ≤ h + p) → ∫ w, wt w ∂μL = 1 →
        h * ∫ w, (∑ j, (w j : ℝ) - (K + 1) * m) * wt w ∂μL ≤ NV := fun wt hwm hw0 hw1 hwE =>
      le_ciInf fun z => weighted ρ hρ h p hh hp wt hwm hw0 hw1 hwE z
    -- the level `r*` with `1 - (1 - r*)^(K+1) = α`
    obtain ⟨rs, ⟨hrs0, hrs1⟩, hrs⟩ : ∃ rs ∈ Icc (0 : ℝ) 1, 1 - (1 - rs) ^ (K + 1) = α := by
      have hc : ContinuousOn (fun r : ℝ => 1 - (1 - r) ^ (K + 1)) (Icc 0 1) := by fun_prop
      have := intermediate_value_Icc (zero_le_one' ℝ) hc
      have hmem : α ∈ Icc ((fun r : ℝ => 1 - (1 - r) ^ (K + 1)) 0)
          ((fun r : ℝ => 1 - (1 - r) ^ (K + 1)) 1) := by
        simp only [sub_zero, one_pow, sub_self, zero_pow (Nat.succ_ne_zero K)]
        exact ⟨hα0.le, hα1.le⟩
      exact this hmem
    have hrs1' : rs < 1 := by
      rcases lt_or_eq_of_le hrs1 with h1 | h1
      · exact h1
      · rw [h1, sub_self, zero_pow (Nat.succ_ne_zero K), sub_zero] at hrs; linarith
    have hrs0' : 0 < rs := by
      rcases lt_or_eq_of_le hrs0 with h1 | h1
      · exact h1
      · rw [← h1, sub_zero, one_pow, sub_self] at hrs; linarith
    obtain ⟨ys, hys0, hq1, hq2⟩ := quantile ρ rs hrs0' hrs1'
    have hint_cw0 : ∀ y : ℝ, ∫ x, cw y 0 x ∂ρ = ρ.real {x : ℝ≥0 | y < (x : ℝ)} := by
      intro y
      simp only [cw_zero]
      rw [show (fun x : ℝ≥0 => ({t : ℝ | y < t}.indicator (1 : ℝ → ℝ) (x : ℝ)))
          = {x : ℝ≥0 | y < (x : ℝ)}.indicator 1 from by
            funext x; by_cases hx : y < (x : ℝ) <;> simp [hx]]
      rw [integral_indicator_one (measurableSet_lt measurable_const measurable_coe_nnreal_real)]
    have hint_cw1 : ∀ y : ℝ, ∫ x, cw y 1 x ∂ρ = ρ.real {x : ℝ≥0 | y ≤ (x : ℝ)} := by
      intro y
      simp only [cw_one]
      rw [show (fun x : ℝ≥0 => ({t : ℝ | y ≤ t}.indicator (1 : ℝ → ℝ) (x : ℝ)))
          = {x : ℝ≥0 | y ≤ (x : ℝ)}.indicator 1 from by
            funext x; by_cases hx : y ≤ (x : ℝ) <;> simp [hx]]
      rw [integral_indicator_one (measurableSet_le measurable_const measurable_coe_nnreal_real)]
    by_cases hcase : m ≤ ys
    · -- Case A: a fractional threshold at the quantile with `q = α`
      have hind : Integrable (fun x : ℝ≥0 => if (x : ℝ) = ys then (1 : ℝ) else 0) ρ := by
        refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (Eventually.of_forall fun x => ?_)
        · exact (Measurable.ite (measurableSet_eq_fun measurable_coe_nnreal_real measurable_const)
            measurable_const measurable_const).aestronglyMeasurable
        · split_ifs <;> simp
      have haff : ∀ θ : ℝ, ∫ x, cw ys θ x ∂ρ
          = ∫ x, cw ys 0 x ∂ρ + θ * ∫ x, (if (x : ℝ) = ys then (1 : ℝ) else 0) ∂ρ := by
        intro θ
        rw [← integral_const_mul, ← integral_add (cw_int ρ le_rfl zero_le_one) (hind.const_mul θ)]
        exact integral_congr_ae (Eventually.of_forall fun x => cw_affine ys θ x)
      obtain ⟨θ, ⟨hθ0, hθ1⟩, hθ⟩ : ∃ θ ∈ Icc (0 : ℝ) 1, ∫ x, cw ys θ x ∂ρ = rs := by
        have hc : ContinuousOn (fun θ : ℝ => ∫ x, cw ys 0 x ∂ρ
            + θ * ∫ x, (if (x : ℝ) = ys then (1 : ℝ) else 0) ∂ρ) (Icc 0 1) := by fun_prop
        have := intermediate_value_Icc (zero_le_one' ℝ) hc
        have hmem : rs ∈ Icc ((fun θ : ℝ => ∫ x, cw ys 0 x ∂ρ
              + θ * ∫ x, (if (x : ℝ) = ys then (1 : ℝ) else 0) ∂ρ) 0)
            ((fun θ : ℝ => ∫ x, cw ys 0 x ∂ρ
              + θ * ∫ x, (if (x : ℝ) = ys then (1 : ℝ) else 0) ∂ρ) 1) := by
          simp only [zero_mul, add_zero, one_mul]
          have h1 := haff 1
          rw [one_mul] at h1
          rw [← h1, hint_cw0, hint_cw1]
          exact ⟨hq1, hq2⟩
        obtain ⟨θ, hθI, hθe⟩ := this hmem
        exact ⟨θ, hθI, by rw [haff θ]; exact hθe⟩
      have hq : 1 - (1 - ∫ x, cw ys θ x ∂ρ) ^ (K + 1) = α := by rw [hθ, hrs]
      -- weight `χ / α`
      have hchi_i := chi_int (K := K) (y := ys) ρ hθ0 hθ1
      have hw := hwNV (fun w => chi ys θ w / α) ((chi_meas ys θ).div_const α)
        (fun w => div_nonneg (chi_bounds (y := ys) hθ0 hθ1 w).1 hα0.le)
        (fun w => by
          have e : h * (chi ys θ w / α) = (h + p) * chi ys θ w := by rw [hα]; field_simp
          rw [e]
          have := (chi_bounds (y := ys) hθ0 hθ1 w).2
          nlinarith)
        (by rw [integral_div, int_chi ρ hθ0 hθ1, hq, div_self hα0.ne'])
      have hcov := cov_ineq (K := K) (y := ys) ρ hρ hθ0 hθ1 hcase
      have hvc := vc_eq (K := K) (y := ys) ρ hρ hθ0 hθ1 m
      rw [hq] at hvc
      have hcovE : ∫ w, (∑ j, (w j : ℝ) - (K + 1) * m) * (chi ys θ w / α) ∂μL
          = (∫ w, (∑ j, (w j : ℝ) - (K + 1) * m) * chi ys θ w ∂μL) / α := by
        rw [← integral_div]; congr 1; funext w; ring
      rw [hcovE] at hw
      have h1q : (1 - ∫ x, cw ys θ x ∂ρ) ^ (K + 1) = 1 - α := by linarith [hq]
      rw [h1q, hvc] at hcov
      set E := ∫ w, max (vmax w - ys) 0 ∂μL
      -- `p ((ys - m) α + E) ≤ NV`
      have key : p * ((ys - m) * α + E) ≤ NV := by
        have h2 : h * ((1 - α) * ((ys - m) * α + E) / α) ≤ NV := by
          refine le_trans ?_ hw
          gcongr
        have h3 : h * ((1 - α) * ((ys - m) * α + E) / α) = p * ((ys - m) * α + E) := by
          rw [← hαp, hα]; field_simp
        linarith
      refine ⟨ys, hys0, ?_⟩
      show (h + p) * (α * ys + ∫ w, max (vmax w - ys) 0 ∂μL) ≤ (1 + h / p) * NV + h * m
      have hfac : (1 + h / p) * (p * ((ys - m) * α + E)) = (h + p) * ((ys - m) * α + E) := by
        field_simp; ring
      have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 1 + h / p)
      rw [hfac] at this
      nlinarith [hαh]
    · -- Case B: the threshold `m` with `q ≤ α`
      rw [not_le] at hcase
      have hθ0 : (0 : ℝ) ≤ 0 := le_rfl
      have hθ1 : (0 : ℝ) ≤ 1 := zero_le_one
      set r := ∫ x, cw m 0 x ∂ρ with hr
      have hrle : r ≤ rs := by
        rw [hr, hint_cw0]
        refine le_trans (measureReal_mono fun x (hx : m < (x : ℝ)) => ?_) hq1
        show ys < (x : ℝ); linarith
      have hr0 : 0 ≤ r := integral_nonneg fun x => cw_nn (y := m) le_rfl (x : ℝ)
      set q := 1 - (1 - r) ^ (K + 1) with hq
      have hqα : q ≤ α := by
        rw [hq, ← hrs]
        have : (1 - rs) ^ (K + 1) ≤ (1 - r) ^ (K + 1) :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
        linarith
      have hq1 : q < 1 := by
        have : 0 < (1 - r) ^ (K + 1) := pow_pos (by linarith) _
        linarith
      have hqne : (1 - q) ≠ 0 := (by linarith : (0 : ℝ) < 1 - q).ne'
      have hchi_i := chi_int (K := K) (y := m) ρ hθ0 hθ1
      have hchiE : ∫ w, chi m 0 w ∂μL = q := int_chi ρ hθ0 hθ1
      set a := 1 / α with ha
      set b := (α - q) / (α * (1 - q)) with hb
      have hb0 : 0 ≤ b := div_nonneg (by linarith) (mul_nonneg hα0.le (by linarith))
      have hba : b ≤ a := by
        rw [hb, ha, div_le_div_iff₀ (mul_pos hα0 (by linarith)) hα0]
        nlinarith
      have hw := hwNV (fun w => a * chi m 0 w + b * (1 - chi m 0 w))
        (((chi_meas m 0).const_mul a).add ((measurable_const.sub (chi_meas m 0)).const_mul b))
        (fun w => by
          have := chi_bounds (y := m) hθ0 hθ1 w
          have ha0 : 0 ≤ a := by positivity
          nlinarith [this.1, this.2])
        (fun w => by
          have := chi_bounds (y := m) hθ0 hθ1 w
          have hha : h * a = h + p := by rw [ha, hα]; field_simp
          nlinarith [this.1, this.2, mul_le_mul_of_nonneg_left hba hh.le])
        (by
          have hi1 : Integrable (fun w : Fin (K + 1) → ℝ≥0 => a * chi m 0 w) μL :=
            hchi_i.const_mul a
          have hi2 : Integrable (fun w : Fin (K + 1) → ℝ≥0 => b * (1 - chi m 0 w)) μL :=
            ((integrable_const 1).sub hchi_i).const_mul b
          rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul,
            integral_sub (integrable_const 1) hchi_i, hchiE]
          simp only [integral_const, probReal_univ, one_smul]
          rw [ha, hb]; field_simp; ring)
      have hSc : Integrable (fun w : Fin (K + 1) → ℝ≥0 => ∑ j, (w j : ℝ) - (K + 1) * m) μL :=
        hS.sub (integrable_const _)
      have hSchi : Integrable (fun w => (∑ j, (w j : ℝ) - (K + 1) * m) * chi m 0 w) μL :=
        hSc.mul_bdd (c := 1) (chi_meas m 0).aestronglyMeasurable
          (Eventually.of_forall (chi_norm hθ0 hθ1))
      have hS0 : ∫ w, (∑ j, (w j : ℝ) - (K + 1) * m) ∂μL = 0 := by
        rw [integral_sub hS (integrable_const _), sum_mean ρ hρ, ← hm]; simp [μL]
      set C := ∫ w, (∑ j, (w j : ℝ) - (K + 1) * m) * chi m 0 w ∂μL with hC
      have hlin : ∫ w, (∑ j, (w j : ℝ) - (K + 1) * m) * (a * chi m 0 w + b * (1 - chi m 0 w)) ∂μL
          = (a - b) * C := by
        have e : (fun w : Fin (K + 1) → ℝ≥0 =>
            (∑ j, (w j : ℝ) - (K + 1) * m) * (a * chi m 0 w + b * (1 - chi m 0 w)))
            = fun w => (a - b) * ((∑ j, (w j : ℝ) - (K + 1) * m) * chi m 0 w)
              + b * (∑ j, (w j : ℝ) - (K + 1) * m) := by
          funext w; ring
        rw [e, integral_add (hSchi.const_mul _) (hSc.const_mul _), integral_const_mul,
          integral_const_mul, hS0, mul_zero, add_zero]
      rw [hlin] at hw
      have hcov := cov_ineq (K := K) (y := m) ρ hρ hθ0 hθ1 le_rfl
      have hvc := vc_eq (K := K) (y := m) ρ hρ hθ0 hθ1 m
      rw [← hr, ← hq, sub_self, zero_mul, zero_add] at hvc
      rw [← hr, hvc] at hcov
      set E := ∫ w, max (vmax w - m) 0 ∂μL
      have hE0 : 0 ≤ E := integral_nonneg fun w => le_max_right _ _
      have h1q : (1 - r) ^ (K + 1) = 1 - q := by rw [hq]; ring
      rw [h1q] at hcov
      -- `p E ≤ NV`
      have hab : a - b = (1 - α) / (α * (1 - q)) := by
        rw [ha, hb]; field_simp; ring
      have key : p * E ≤ NV := by
        have h2 : h * ((a - b) * ((1 - q) * E)) ≤ NV := by
          refine le_trans ?_ hw
          have hab0 : 0 ≤ a - b := by linarith
          gcongr
        have h3 : h * ((a - b) * ((1 - q) * E)) = p * E := by
          rw [hab, ← hαp, hα]; field_simp
        linarith
      refine ⟨m, hm0, ?_⟩
      show (h + p) * (α * m + E) ≤ (1 + h / p) * NV + h * m
      have hfac : (1 + h / p) * (p * E) = (h + p) * E := by field_simp; ring
      have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 1 + h / p)
      rw [hfac] at this
      calc (h + p) * (α * m + E) = (h + p) * α * m + (h + p) * E := by ring
        _ = h * m + (h + p) * E := by rw [hαh]
        _ ≤ (1 + h / p) * NV + h * m := by linarith
