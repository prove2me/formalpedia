-- Prove2me | solution 1 for OWMR.arb_protected_newsvendor
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T12:52:27.399647+00:00
-- url     : https://prove2.me/submissions/d9e14ac4-cc87-431f-b6f8-ec8c9e210591

import Definitions.Def_owmr_consolidation_policy
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
Association gives the protected newsvendor comparison (C.20)-(C.21): the newsvendor cost of the
batch retailers' lead-time demand is at most that of total lead-time demand.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR

namespace OWMR.LAaux

variable {n : ℕ}

lemma whLoss_abs_le (h p y : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) : |whLoss h p y| ≤ (h + p) * |y| := by
  unfold whLoss
  have h1 : 0 ≤ h * max y 0 + p * max (-y) 0 := by positivity
  rw [abs_of_nonneg h1]
  have a1 : max y 0 ≤ |y| := max_le (le_abs_self y) (abs_nonneg y)
  have a2 : max (-y) 0 ≤ |y| := max_le (neg_le_abs y) (abs_nonneg y)
  have b1 : h * max y 0 ≤ h * |y| := mul_le_mul_of_nonneg_left a1 hh
  have b2 : p * max (-y) 0 ≤ p * |y| := mul_le_mul_of_nonneg_left a2 hp
  nlinarith

lemma whLoss_nn (h p y : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) : 0 ≤ whLoss h p y := by
  unfold whLoss; positivity

lemma whLoss_cont (h p : ℝ) : Continuous (whLoss h p) := by
  unfold whLoss; fun_prop

lemma int_whLoss {α : Type*} [MeasurableSpace α] {μ : Measure α} (h p : ℝ) (hh : 0 ≤ h)
    (hp : 0 ≤ p) {g : α → ℝ} (hg : Integrable g μ) :
    Integrable (fun x => whLoss h p (g x)) μ := by
  refine Integrable.mono' (hg.norm.const_mul (h + p))
    ((whLoss_cont h p).comp_aestronglyMeasurable hg.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using whLoss_abs_le h p (g x) hh hp

/-- Supporting line of the convex function `t ↦ φ(a - t)` at `t`. -/
lemma whLoss_support (h p a t t' : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) :
    whLoss h p (a - t) + (if a < t then p else -h) * (t' - t) ≤ whLoss h p (a - t') := by
  unfold whLoss
  have l1 : 0 ≤ max (a - t') 0 := le_max_right _ _
  have l2 : 0 ≤ max (-(a - t')) 0 := le_max_right _ _
  have l3 : a - t' ≤ max (a - t') 0 := le_max_left _ _
  have l4 : -(a - t') ≤ max (-(a - t')) 0 := le_max_left _ _
  have m1 : 0 ≤ h * max (a - t') 0 := mul_nonneg hh l1
  have m2 : 0 ≤ p * max (-(a - t')) 0 := mul_nonneg hp l2
  have m3 : h * (a - t') ≤ h * max (a - t') 0 := mul_le_mul_of_nonneg_left l3 hh
  have m4 : p * (-(a - t')) ≤ p * max (-(a - t')) 0 := mul_le_mul_of_nonneg_left l4 hp
  split_ifs with hat
  · have e1 : max (a - t) 0 = 0 := max_eq_right (by linarith)
    have e2 : max (-(a - t)) 0 = t - a := by rw [max_eq_left (by linarith)]; ring
    rw [e1, e2]
    nlinarith
  · have e1 : max (a - t) 0 = a - t := max_eq_left (by linarith)
    have e2 : max (-(a - t)) 0 = 0 := max_eq_right (by linarith)
    rw [e1, e2]
    nlinarith

lemma int_coord (N : Network n) (hN : N.Standing) (i : Fin n) :
    Integrable (fun x : DemandVec n => ((x i : ℝ≥0) : ℝ)) N.μ := by
  have h1 := integrable_toReal_of_lintegral_ne_top
    (f := fun x : DemandVec n => ((x i : ℝ≥0) : ℝ≥0∞))
    ((measurable_pi_apply i).coe_nnreal_ennreal.aemeasurable) (hN.mean_lt_top i).ne
  simpa using h1

lemma meas_psum (s : Finset (Fin n)) :
    Measurable fun x : DemandVec n => ∑ i ∈ s, ((x i : ℝ≥0) : ℝ) :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).coe_nnreal_real

lemma int_psum (N : Network n) (hN : N.Standing) (s : Finset (Fin n)) :
    Integrable (fun x : DemandVec n => ∑ i ∈ s, ((x i : ℝ≥0) : ℝ)) N.μ :=
  integrable_finsetSum _ fun i _ => int_coord N hN i

lemma mono_psum (s : Finset (Fin n)) :
    Monotone fun x : DemandVec n => ∑ i ∈ s, ((x i : ℝ≥0) : ℝ) := fun x x' hxx' =>
  Finset.sum_le_sum fun i _ => NNReal.coe_le_coe.2 (hxx' i)

/-- Association: `ℙ(X > z) 𝔼 Y ≤ 𝔼[1{X > z} Y]` for the totals `X` over `P` and `Y` over `Pᶜ`. -/
lemma assoc_cov (N : Network n) (hN : N.Standing) (hA : N.Associated) (P : Finset (Fin n))
    (z : ℝ) :
    N.μ.real {x : DemandVec n | z < ∑ i ∈ P, ((x i : ℝ≥0) : ℝ)}
        * ∫ x, ∑ i ∈ Pᶜ, ((x i : ℝ≥0) : ℝ) ∂N.μ
      ≤ ∫ x, {x : DemandVec n | z < ∑ i ∈ P, ((x i : ℝ≥0) : ℝ)}.indicator
          (fun x => ∑ i ∈ Pᶜ, ((x i : ℝ≥0) : ℝ)) x ∂N.μ := by
  set S : Set (DemandVec n) := {x | z < ∑ i ∈ P, ((x i : ℝ≥0) : ℝ)} with hS
  set Y : DemandVec n → ℝ := fun x => ∑ i ∈ Pᶜ, ((x i : ℝ≥0) : ℝ) with hY
  have hSm : MeasurableSet S := measurableSet_lt measurable_const (meas_psum P)
  have hYm : Measurable Y := meas_psum Pᶜ
  have hYi : Integrable Y N.μ := int_psum N hN Pᶜ
  have hY0 : ∀ x, 0 ≤ Y x := fun x => Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _
  set u : DemandVec n → ℝ := S.indicator fun _ => 1 with hu
  have hum : Measurable u := measurable_const.indicator hSm
  have humono : Monotone u := by
    intro x x' hxx'
    by_cases hx : x ∈ S
    · have hx' : x' ∈ S := lt_of_lt_of_le hx (mono_psum P hxx')
      simp [hu, Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · simp only [hu, Set.indicator_of_notMem hx]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) x'
  have hub : ∃ C, ∀ x, |u x| ≤ C := ⟨1, fun x => by by_cases hx : x ∈ S <;> simp [hu, hx]⟩
  set v : ℕ → DemandVec n → ℝ := fun b x => min (Y x) b with hv
  have hvabs : ∀ (b : ℕ) x, |v b x| = v b x := fun b x =>
    abs_of_nonneg (le_min (hY0 x) (Nat.cast_nonneg b))
  have hvm : ∀ b, Measurable (v b) := fun b => hYm.min measurable_const
  have key : ∀ b : ℕ, (∫ x, u x ∂N.μ) * (∫ x, v b x ∂N.μ) ≤ ∫ x, S.indicator (v b) x ∂N.μ := by
    intro b
    have h := hA u (v b) hum (hvm b) humono
      (fun x x' hxx' => min_le_min_right _ (mono_psum Pᶜ hxx')) hub
      ⟨b, fun x => by rw [hvabs]; exact min_le_right _ _⟩
    refine h.trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun x => ?_)))
    by_cases hx : x ∈ S <;> simp [hu, hx]
  have hu1 : ∫ x, u x ∂N.μ = N.μ.real S := by
    rw [hu, integral_indicator_const _ hSm, smul_eq_mul, mul_one]
  have hpt : ∀ x, Tendsto (fun b : ℕ => v b x) atTop (𝓝 (Y x)) := fun x =>
    tendsto_atTop_of_eventually_const (i₀ := ⌈Y x⌉₊) fun b hb =>
      min_eq_left ((Nat.le_ceil _).trans (Nat.cast_le.2 hb))
  have hlim1 : Tendsto (fun b : ℕ => ∫ x, v b x ∂N.μ) atTop (𝓝 (∫ x, Y x ∂N.μ)) := by
    refine tendsto_integral_of_dominated_convergence Y (fun b => (hvm b).aestronglyMeasurable)
      hYi (fun b => Eventually.of_forall fun x => ?_) (Eventually.of_forall hpt)
    rw [Real.norm_eq_abs, hvabs]; exact min_le_left _ _
  have hlim2 : Tendsto (fun b : ℕ => ∫ x, S.indicator (v b) x ∂N.μ) atTop
      (𝓝 (∫ x, S.indicator Y x ∂N.μ)) := by
    refine tendsto_integral_of_dominated_convergence Y
      (fun b => ((hvm b).indicator hSm).aestronglyMeasurable) hYi
      (fun b => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, hvabs]; exact min_le_left _ _
      · rw [Set.indicator_of_notMem hx, norm_zero]; exact hY0 x
    · by_cases hx : x ∈ S
      · simp only [Set.indicator_of_mem hx]; exact hpt x
      · simp only [Set.indicator_of_notMem hx]; exact tendsto_const_nhds
  have := le_of_tendsto_of_tendsto' (hlim1.const_mul (∫ x, u x ∂N.μ)) hlim2 key
  rwa [hu1] at this

/-- One period: replacing the complementary demand by its mean cannot raise the expected loss. -/
lemma one_period (N : Network n) (hN : N.Standing) (hA : N.Associated) (P : Finset (Fin n))
    (a : ℝ) :
    ∫ x, whLoss N.h N.p (a - ∑ i ∈ P, ((x i : ℝ≥0) : ℝ)
        - ∫ y, ∑ i ∈ Pᶜ, ((y i : ℝ≥0) : ℝ) ∂N.μ) ∂N.μ
      ≤ ∫ x, whLoss N.h N.p (a - ∑ i ∈ P, ((x i : ℝ≥0) : ℝ) - ∑ i ∈ Pᶜ, ((x i : ℝ≥0) : ℝ))
          ∂N.μ := by
  set m := ∫ y, ∑ i ∈ Pᶜ, ((y i : ℝ≥0) : ℝ) ∂N.μ with hm
  set X : DemandVec n → ℝ := fun x => ∑ i ∈ P, ((x i : ℝ≥0) : ℝ) with hX
  set Y : DemandVec n → ℝ := fun x => ∑ i ∈ Pᶜ, ((x i : ℝ≥0) : ℝ) with hY
  set S : Set (DemandVec n) := {x | a - m < X x} with hS
  have hh := hN.h_pos.le
  have hp := hN.p_pos.le
  have hXi : Integrable X N.μ := int_psum N hN P
  have hYi : Integrable Y N.μ := int_psum N hN Pᶜ
  have hSm : MeasurableSet S := measurableSet_lt measurable_const (meas_psum P)
  have hpt : ∀ x, whLoss N.h N.p (a - X x - m)
      + ((N.h + N.p) * S.indicator (fun x => Y x - m) x - N.h * (Y x - m))
      ≤ whLoss N.h N.p (a - X x - Y x) := by
    intro x
    have h0 := whLoss_support N.h N.p a (X x + m) (X x + Y x) hh hp
    have e1 : a - (X x + m) = a - X x - m := by ring
    have e2 : a - (X x + Y x) = a - X x - Y x := by ring
    rw [e1, e2] at h0
    refine le_of_eq_of_le ?_ h0
    by_cases hx : x ∈ S
    · have hlt : a < X x + m := by
        have : a - m < X x := hx
        linarith
      rw [if_pos hlt, Set.indicator_of_mem hx]; ring
    · have hlt : ¬ a < X x + m := by
        intro h'
        exact hx (show a - m < X x by linarith)
      rw [if_neg hlt, Set.indicator_of_notMem hx]; ring
  have hi1 : Integrable (fun x => whLoss N.h N.p (a - X x - m)) N.μ :=
    int_whLoss _ _ hh hp (((integrable_const a).sub hXi).sub (integrable_const m))
  have hi2 : Integrable (fun x => whLoss N.h N.p (a - X x - Y x)) N.μ :=
    int_whLoss _ _ hh hp (((integrable_const a).sub hXi).sub hYi)
  have hYc : Integrable (fun x => Y x - m) N.μ := hYi.sub (integrable_const m)
  have hi3 : Integrable (fun x => S.indicator (fun x => Y x - m) x) N.μ := hYc.indicator hSm
  have hcov : 0 ≤ ∫ x, S.indicator (fun x => Y x - m) x ∂N.μ := by
    have e : (fun x => S.indicator (fun x => Y x - m) x)
        = fun x => S.indicator Y x - S.indicator (fun _ => m) x := by
      funext x; by_cases hx : x ∈ S <;> simp [hx]
    rw [e, integral_sub (hYi.indicator hSm) ((integrable_const m).indicator hSm),
      integral_indicator_const _ hSm, smul_eq_mul]
    have := assoc_cov N hN hA P (a - m)
    linarith
  have hYm0 : ∫ x, (Y x - m) ∂N.μ = 0 := by
    rw [integral_sub hYi (integrable_const m), integral_const]
    simp [hm]
  have hj : Integrable (fun x => (N.h + N.p) * S.indicator (fun x => Y x - m) x
      - N.h * (Y x - m)) N.μ := (hi3.const_mul _).sub (hYc.const_mul _)
  calc ∫ x, whLoss N.h N.p (a - X x - m) ∂N.μ
      ≤ ∫ x, whLoss N.h N.p (a - X x - m) ∂N.μ
          + ((N.h + N.p) * ∫ x, S.indicator (fun x => Y x - m) x ∂N.μ
            - N.h * ∫ x, (Y x - m) ∂N.μ) := by
        rw [hYm0]; nlinarith [hcov]
    _ = ∫ x, (whLoss N.h N.p (a - X x - m)
          + ((N.h + N.p) * S.indicator (fun x => Y x - m) x - N.h * (Y x - m))) ∂N.μ := by
        rw [integral_add hi1 hj, integral_sub (hi3.const_mul _) (hYc.const_mul _),
          integral_const_mul, integral_const_mul]
    _ ≤ ∫ x, whLoss N.h N.p (a - X x - Y x) ∂N.μ := integral_mono (hi1.add hj) hi2 hpt

lemma one_period_lint (N : Network n) (hN : N.Standing) (hA : N.Associated)
    (P : Finset (Fin n)) (a : ℝ) :
    ∫⁻ x, ENNReal.ofReal (whLoss N.h N.p (a - ∑ i ∈ P, ((x i : ℝ≥0) : ℝ)
        - ∫ y, ∑ i ∈ Pᶜ, ((y i : ℝ≥0) : ℝ) ∂N.μ)) ∂N.μ
      ≤ ∫⁻ x, ENNReal.ofReal (whLoss N.h N.p (a - ∑ i ∈ P, ((x i : ℝ≥0) : ℝ)
          - ∑ i ∈ Pᶜ, ((x i : ℝ≥0) : ℝ))) ∂N.μ := by
  have hh := hN.h_pos.le
  have hp := hN.p_pos.le
  have hg1 : Integrable (fun x : DemandVec n => a - ∑ i ∈ P, ((x i : ℝ≥0) : ℝ)
      - ∫ y, ∑ i ∈ Pᶜ, ((y i : ℝ≥0) : ℝ) ∂N.μ) N.μ :=
    ((integrable_const a).sub (int_psum N hN P)).sub (integrable_const _)
  have hg2 : Integrable (fun x : DemandVec n => a - ∑ i ∈ P, ((x i : ℝ≥0) : ℝ)
      - ∑ i ∈ Pᶜ, ((x i : ℝ≥0) : ℝ)) N.μ :=
    ((integrable_const a).sub (int_psum N hN P)).sub (int_psum N hN Pᶜ)
  have hi1 : Integrable (fun x : DemandVec n => whLoss N.h N.p (a - ∑ i ∈ P, ((x i : ℝ≥0) : ℝ)
      - ∫ y, ∑ i ∈ Pᶜ, ((y i : ℝ≥0) : ℝ) ∂N.μ)) N.μ := int_whLoss _ _ hh hp hg1
  have hi2 : Integrable (fun x : DemandVec n => whLoss N.h N.p (a - ∑ i ∈ P, ((x i : ℝ≥0) : ℝ)
      - ∑ i ∈ Pᶜ, ((x i : ℝ≥0) : ℝ))) N.μ := int_whLoss _ _ hh hp hg2
  rw [← ofReal_integral_eq_lintegral_ofReal hi1
      (Eventually.of_forall fun x => whLoss_nn _ _ _ hh hp),
    ← ofReal_integral_eq_lintegral_ofReal hi2
      (Eventually.of_forall fun x => whLoss_nn _ _ _ hh hp)]
  exact ENNReal.ofReal_le_ofReal (one_period N hN hA P a)

lemma lintegral_pi_succ' (N : Network n) (T : ℕ)
    {F : DemandVec n × (Fin T → DemandVec n) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F (z 0, Fin.tail z) ∂(Measure.pi fun _ : Fin (T + 1) => N.μ)
      = ∫⁻ y, ∫⁻ z', F (y, z') ∂(Measure.pi fun _ : Fin T => N.μ) ∂N.μ := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (T + 1) => N.μ) 0
  have key : ∫⁻ z, F (z 0, Fin.tail z) ∂(Measure.pi fun _ : Fin (T + 1) => N.μ)
      = ∫⁻ z, F (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T + 1) => DemandVec n) 0 z)
          ∂(Measure.pi fun _ : Fin (T + 1) => N.μ) := by
    refine lintegral_congr fun z => ?_
    simp [MeasurableEquiv.piFinSuccAbove_apply]
  rw [key, hmp.lintegral_comp hF, lintegral_prod _ hF.aemeasurable]

lemma meas_vsum (T : ℕ) (s : Finset (Fin n)) :
    Measurable fun v : Fin T → DemandVec n => ∑ ℓ, ∑ i ∈ s, ((v ℓ i : ℝ≥0) : ℝ) :=
  Finset.measurable_sum _ fun ℓ _ => (meas_psum s).comp (measurable_pi_apply ℓ)

/-- Many periods: replacing every period's complementary demand by its mean. -/
lemma multi (N : Network n) (hN : N.Standing) (hA : N.Associated) (P : Finset (Fin n)) :
    ∀ (L : ℕ) (a : ℝ),
    ∫⁻ v, ENNReal.ofReal (whLoss N.h N.p (a - L * ∫ y, ∑ i ∈ Pᶜ, ((y i : ℝ≥0) : ℝ) ∂N.μ
        - ∑ ℓ, ∑ i ∈ P, ((v ℓ i : ℝ≥0) : ℝ))) ∂(Measure.pi fun _ : Fin L => N.μ)
      ≤ ∫⁻ v, ENNReal.ofReal (whLoss N.h N.p (a - ∑ ℓ, ∑ i, ((v ℓ i : ℝ≥0) : ℝ)))
          ∂(Measure.pi fun _ : Fin L => N.μ) := by
  set m := ∫ y, ∑ i ∈ Pᶜ, ((y i : ℝ≥0) : ℝ) ∂N.μ with hm
  have hc : Continuous fun y => ENNReal.ofReal (whLoss N.h N.p y) :=
    ENNReal.continuous_ofReal.comp (whLoss_cont _ _)
  have hsplit : ∀ x : DemandVec n, ∑ i, ((x i : ℝ≥0) : ℝ)
      = ∑ i ∈ P, ((x i : ℝ≥0) : ℝ) + ∑ i ∈ Pᶜ, ((x i : ℝ≥0) : ℝ) := fun x =>
    (Finset.sum_add_sum_compl P _).symm
  intro L
  induction L with
  | zero => intro a; simp
  | succ L ih =>
    intro a
    have e1 : ∀ v : Fin (L + 1) → DemandVec n,
        ENNReal.ofReal (whLoss N.h N.p (a - ((L + 1 : ℕ) : ℝ) * m
          - ∑ ℓ, ∑ i ∈ P, ((v ℓ i : ℝ≥0) : ℝ)))
        = (fun q : DemandVec n × (Fin L → DemandVec n) =>
            ENNReal.ofReal (whLoss N.h N.p ((a - L * m - ∑ ℓ, ∑ i ∈ P, ((q.2 ℓ i : ℝ≥0) : ℝ))
              - ∑ i ∈ P, ((q.1 i : ℝ≥0) : ℝ) - m))) (v 0, Fin.tail v) := by
      intro v
      simp only [Fin.sum_univ_succ, Fin.tail, Nat.cast_succ]
      congr 2; ring
    have e2 : ∀ v : Fin (L + 1) → DemandVec n,
        ENNReal.ofReal (whLoss N.h N.p (a - ∑ ℓ, ∑ i, ((v ℓ i : ℝ≥0) : ℝ)))
        = (fun q : DemandVec n × (Fin L → DemandVec n) =>
            ENNReal.ofReal (whLoss N.h N.p ((a - ∑ i, ((q.1 i : ℝ≥0) : ℝ))
              - ∑ ℓ, ∑ i, ((q.2 ℓ i : ℝ≥0) : ℝ)))) (v 0, Fin.tail v) := by
      intro v
      simp only [Fin.sum_univ_succ, Fin.tail]
      congr 2; ring
    have hm1 : Measurable fun q : DemandVec n × (Fin L → DemandVec n) =>
        ENNReal.ofReal (whLoss N.h N.p ((a - L * m - ∑ ℓ, ∑ i ∈ P, ((q.2 ℓ i : ℝ≥0) : ℝ))
          - ∑ i ∈ P, ((q.1 i : ℝ≥0) : ℝ) - m)) :=
      hc.measurable.comp ((((measurable_const.sub ((meas_vsum L P).comp measurable_snd)).sub
        ((meas_psum P).comp measurable_fst)).sub measurable_const))
    have hm2 : Measurable fun q : DemandVec n × (Fin L → DemandVec n) =>
        ENNReal.ofReal (whLoss N.h N.p ((a - ∑ i, ((q.1 i : ℝ≥0) : ℝ))
          - ∑ ℓ, ∑ i, ((q.2 ℓ i : ℝ≥0) : ℝ))) :=
      hc.measurable.comp ((measurable_const.sub ((meas_psum Finset.univ).comp measurable_fst)).sub
        ((meas_vsum L Finset.univ).comp measurable_snd))
    simp only [e1, e2]
    rw [lintegral_pi_succ' N L hm1, lintegral_pi_succ' N L hm2]
    have hm3 : Measurable fun q : (Fin L → DemandVec n) × DemandVec n =>
        ENNReal.ofReal (whLoss N.h N.p
          ((a - L * m - ∑ ℓ, ∑ i ∈ P, ((q.1 ℓ i : ℝ≥0) : ℝ)) - ∑ i ∈ P, ((q.2 i : ℝ≥0) : ℝ)
            - ∑ i ∈ Pᶜ, ((q.2 i : ℝ≥0) : ℝ))) :=
      hc.measurable.comp ((((measurable_const.sub ((meas_vsum L P).comp measurable_fst)).sub
        ((meas_psum P).comp measurable_snd)).sub ((meas_psum Pᶜ).comp measurable_snd)))
    calc ∫⁻ y, ∫⁻ z', ENNReal.ofReal (whLoss N.h N.p
            ((a - L * m - ∑ ℓ, ∑ i ∈ P, ((z' ℓ i : ℝ≥0) : ℝ)) - ∑ i ∈ P, ((y i : ℝ≥0) : ℝ) - m))
            ∂(Measure.pi fun _ : Fin L => N.μ) ∂N.μ
        = ∫⁻ z', ∫⁻ y, ENNReal.ofReal (whLoss N.h N.p
            ((a - L * m - ∑ ℓ, ∑ i ∈ P, ((z' ℓ i : ℝ≥0) : ℝ)) - ∑ i ∈ P, ((y i : ℝ≥0) : ℝ) - m))
            ∂N.μ ∂(Measure.pi fun _ : Fin L => N.μ) :=
          lintegral_lintegral_swap (by exact hm1.aemeasurable)
      _ ≤ ∫⁻ z', ∫⁻ y, ENNReal.ofReal (whLoss N.h N.p
            ((a - L * m - ∑ ℓ, ∑ i ∈ P, ((z' ℓ i : ℝ≥0) : ℝ)) - ∑ i ∈ P, ((y i : ℝ≥0) : ℝ)
              - ∑ i ∈ Pᶜ, ((y i : ℝ≥0) : ℝ)))
            ∂N.μ ∂(Measure.pi fun _ : Fin L => N.μ) :=
          lintegral_mono fun z' => one_period_lint N hN hA P _
      _ = ∫⁻ y, ∫⁻ z', ENNReal.ofReal (whLoss N.h N.p
            ((a - L * m - ∑ ℓ, ∑ i ∈ P, ((z' ℓ i : ℝ≥0) : ℝ)) - ∑ i ∈ P, ((y i : ℝ≥0) : ℝ)
              - ∑ i ∈ Pᶜ, ((y i : ℝ≥0) : ℝ)))
            ∂(Measure.pi fun _ : Fin L => N.μ) ∂N.μ :=
          lintegral_lintegral_swap (by exact hm3.aemeasurable)
      _ = ∫⁻ y, ∫⁻ z', ENNReal.ofReal (whLoss N.h N.p
            ((a - ∑ i, ((y i : ℝ≥0) : ℝ)) - L * m - ∑ ℓ, ∑ i ∈ P, ((z' ℓ i : ℝ≥0) : ℝ)))
            ∂(Measure.pi fun _ : Fin L => N.μ) ∂N.μ := by
          refine lintegral_congr fun y => lintegral_congr fun z' => ?_
          rw [hsplit y]; congr 2; ring
      _ ≤ ∫⁻ y, ∫⁻ z', ENNReal.ofReal (whLoss N.h N.p
            ((a - ∑ i, ((y i : ℝ≥0) : ℝ)) - ∑ ℓ, ∑ i, ((z' ℓ i : ℝ≥0) : ℝ)))
            ∂(Measure.pi fun _ : Fin L => N.μ) ∂N.μ :=
          lintegral_mono fun y => ih _

lemma int_vsum (N : Network n) (hN : N.Standing) (L : ℕ) (s : Finset (Fin n)) :
    Integrable (fun v : Fin L → DemandVec n => ∑ ℓ, ∑ i ∈ s, ((v ℓ i : ℝ≥0) : ℝ))
      (Measure.pi fun _ : Fin L => N.μ) := by
  refine integrable_finsetSum _ fun ℓ _ => ?_
  have hmp := measurePreserving_eval (μ := fun _ : Fin L => N.μ) ℓ
  exact (hmp.integrable_comp (meas_psum s).aestronglyMeasurable).2 (int_psum N hN s)

end OWMR.LAaux

open OWMR.LAaux in
theorem solution {n : ℕ} (N : Network n) (hN : N.Standing) (hA : N.Associated)
    (P : Finset (Fin n)) :
    ⨅ z : ℝ, ∫ w, whLoss N.h N.p (z - ∑ j, (w j : ℝ))
        ∂(Measure.pi fun _ : Fin N.L0 =>
          (N.μ.map (fun x : DemandVec n => (∑ i ∈ P, x i : ℝ≥0)) : Measure ℝ≥0))
      ≤ ⨅ y : ℝ, N.fL0 y := by
  have hh := hN.h_pos.le
  have hp := hN.p_pos.le
  set m := ∫ y, ∑ i ∈ Pᶜ, ((y i : ℝ≥0) : ℝ) ∂N.μ with hm
  have hmeasP : Measurable fun x : DemandVec n => ∑ i ∈ P, x i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hmeasD : Measurable fun x : DemandVec n => ∑ i, x i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hmapP : (Measure.pi fun _ : Fin N.L0 => N.μ).map
      (fun v (j : Fin N.L0) => ∑ i ∈ P, v j i)
      = Measure.pi fun _ : Fin N.L0 =>
        (N.μ.map (fun x : DemandVec n => (∑ i ∈ P, x i : ℝ≥0)) : Measure ℝ≥0) :=
    Measure.pi_map_pi (μ := fun _ : Fin N.L0 => N.μ)
      (f := fun (_ : Fin N.L0) (x : DemandVec n) => ∑ i ∈ P, x i) (fun _ => hmeasP.aemeasurable)
  have hmapD : (Measure.pi fun _ : Fin N.L0 => N.μ).map
      (fun v (j : Fin N.L0) => ∑ i, v j i)
      = Measure.pi fun _ : Fin N.L0 => N.aggregate :=
    Measure.pi_map_pi (μ := fun _ : Fin N.L0 => N.μ)
      (f := fun (_ : Fin N.L0) (x : DemandVec n) => ∑ i, x i) (fun _ => hmeasD.aemeasurable)
  have hc : Continuous fun y => whLoss N.h N.p y := whLoss_cont _ _
  have hcs : ∀ c : ℝ, Continuous fun w : Fin N.L0 → ℝ≥0 => whLoss N.h N.p (c - ∑ j, (w j : ℝ)) :=
    fun c => hc.comp (continuous_const.sub (continuous_finsetSum _ fun j _ =>
      NNReal.continuous_coe.comp (continuous_apply j)))
  have hPint : ∀ z, ∫ w, whLoss N.h N.p (z - ∑ j, (w j : ℝ))
      ∂(Measure.pi fun _ : Fin N.L0 =>
          (N.μ.map (fun x : DemandVec n => (∑ i ∈ P, x i : ℝ≥0)) : Measure ℝ≥0))
      = ∫ v, whLoss N.h N.p (z - ∑ j, ∑ i ∈ P, ((v j i : ℝ≥0) : ℝ))
          ∂(Measure.pi fun _ : Fin N.L0 => N.μ) := by
    intro z
    rw [← hmapP]
    have hφ : AEMeasurable (fun (v : Fin N.L0 → DemandVec n) (j : Fin N.L0) => ∑ i ∈ P, v j i)
        (Measure.pi fun _ : Fin N.L0 => N.μ) :=
      (measurable_pi_lambda _ fun j => hmeasP.comp (measurable_pi_apply j)).aemeasurable
    have hf : AEStronglyMeasurable (fun w : Fin N.L0 → ℝ≥0 => whLoss N.h N.p (z - ∑ j, (w j : ℝ)))
        ((Measure.pi fun _ : Fin N.L0 => N.μ).map
          (fun (v : Fin N.L0 → DemandVec n) (j : Fin N.L0) => ∑ i ∈ P, v j i)) :=
      (hcs z).aestronglyMeasurable
    rw [integral_map hφ hf]
    simp [NNReal.coe_sum]
  have hDint : ∀ y, N.fL0 y = ∫ v, whLoss N.h N.p (y - ∑ j, ∑ i, ((v j i : ℝ≥0) : ℝ))
      ∂(Measure.pi fun _ : Fin N.L0 => N.μ) := by
    intro y
    rw [Network.fL0, ← hmapD]
    have hφ : AEMeasurable (fun (v : Fin N.L0 → DemandVec n) (j : Fin N.L0) => ∑ i, v j i)
        (Measure.pi fun _ : Fin N.L0 => N.μ) :=
      (measurable_pi_lambda _ fun j => hmeasD.comp (measurable_pi_apply j)).aemeasurable
    have hf : AEStronglyMeasurable (fun w : Fin N.L0 → ℝ≥0 => whLoss N.h N.p (y - ∑ j, (w j : ℝ)))
        ((Measure.pi fun _ : Fin N.L0 => N.μ).map
          (fun (v : Fin N.L0 → DemandVec n) (j : Fin N.L0) => ∑ i, v j i)) :=
      (hcs y).aestronglyMeasurable
    rw [integral_map hφ hf]
    simp [NNReal.coe_sum]
  refine le_ciInf fun y => ?_
  refine (ciInf_le ⟨0, ?_⟩ (y - N.L0 * m)).trans ?_
  · rintro _ ⟨z, rfl⟩
    exact integral_nonneg fun w => whLoss_nn _ _ _ hh hp
  rw [hPint, hDint]
  have hiP : Integrable (fun v : Fin N.L0 → DemandVec n =>
      whLoss N.h N.p (y - N.L0 * m - ∑ j, ∑ i ∈ P, ((v j i : ℝ≥0) : ℝ)))
      (Measure.pi fun _ : Fin N.L0 => N.μ) :=
    int_whLoss _ _ hh hp ((integrable_const _).sub (int_vsum N hN N.L0 P))
  have hiD : Integrable (fun v : Fin N.L0 → DemandVec n =>
      whLoss N.h N.p (y - ∑ j, ∑ i, ((v j i : ℝ≥0) : ℝ)))
      (Measure.pi fun _ : Fin N.L0 => N.μ) :=
    int_whLoss _ _ hh hp ((integrable_const _).sub (int_vsum N hN N.L0 Finset.univ))
  have h3 := multi N hN hA P N.L0 y
  rw [← ofReal_integral_eq_lintegral_ofReal hiP
      (Eventually.of_forall fun v => whLoss_nn _ _ _ hh hp),
    ← ofReal_integral_eq_lintegral_ofReal hiD
      (Eventually.of_forall fun v => whLoss_nn _ _ _ hh hp)] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun v => whLoss_nn _ _ _ hh hp)).1 h3
