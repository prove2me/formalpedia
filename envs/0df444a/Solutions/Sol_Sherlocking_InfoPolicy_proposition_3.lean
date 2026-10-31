-- Prove2me | solution 1 for Sherlocking.InfoPolicy.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:30:21.238484+00:00
-- url     : https://prove2.me/submissions/198cbe92-8deb-4263-90d0-0626cb2b0457

import Mathlib
import Definitions.Def_Sherlocking_InfoPolicy_Model
import Theorems.Thm_Sherlocking_InfoPolicy_signal3_obedience
import Theorems.Thm_Sherlocking_InfoPolicy_oc0_iff_ineq4

open MeasureTheory Sherlocking.InfoPolicy

namespace SherlockAux

lemma ivl_int_of_bdd {f : ℝ → ℝ} (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  exact Measure.integrableOn_of_bounded (M := M) (by rw [Set.uIoc]; exact measure_Ioc_lt_top.ne)
    hf.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => by simpa using hM x))

lemma meas_alpha (K δ r : ℝ) : Measurable (fun θ => alpha K δ θ r) := by
  unfold alpha; fun_prop

lemma meas_c (K δ r : ℝ) : Measurable (commitProb K δ r) := by
  unfold commitProb
  exact Measurable.ite (measurableSet_Icc (a := thetaP K δ r) (b := 1)) (meas_alpha K δ r)
    measurable_const

structure Facts (K δ r : ℝ) : Prop where
  hK0 : 0 < K
  hδ0 : 0 < δ
  hδ1 : δ < 1
  hr0 : 0 ≤ r
  hrK : r < 1 - K
  hS : thetaS K r = K / (1 - r)
  hS0 : 0 < thetaS K r
  hSP : thetaS K r < thetaP K δ r
  hP1 : thetaP K δ r ≤ 1
  hα : ∀ θ ∈ Set.Icc (thetaP K δ r) 1, 0 ≤ alpha K δ θ r ∧ alpha K δ θ r < 1

lemma facts (K δ r : ℝ) (hδ1 : δ < 1) (hK1 : 1 - δ < K) (hK2 : K < δ) (hr0 : 0 ≤ r)
    (hrK : r < 1 - K) : Facts K δ r := by
  have ha : K < 1 - r := by linarith
  have hK0 : 0 < K := by linarith
  have hδ0 : 0 < δ := by linarith
  have hapos : 0 < 1 - r := by linarith
  have hS : thetaS K r = K / (1 - r) := by unfold thetaS; rw [if_pos ha]
  have hSle1 : K / (1 - r) < 1 := (div_lt_one hapos).mpr ha
  have hS0 : 0 < K / (1 - r) := div_pos hK0 hapos
  have hP_ge : K / (1 - r) < thetaP K δ r := by
    unfold thetaP
    split_ifs with h
    · rw [div_lt_div_iff₀ hapos (by positivity)]
      have := mul_pos (mul_pos hK0 hapos) (sub_pos.mpr hδ1)
      nlinarith
    · linarith
  have hP_le1 : thetaP K δ r ≤ 1 := by
    unfold thetaP
    split_ifs with h
    · exact (div_le_one (by positivity)).mpr h.le
    · exact le_refl _
  refine ⟨hK0, hδ0, hδ1, hr0, hrK, hS, by rw [hS]; exact hS0, by rw [hS]; exact hP_ge,
    hP_le1, ?_⟩
  intro θ hθ
  obtain ⟨hθ1, hθ2⟩ := hθ
  have hθS : K / (1 - r) ≤ θ := hP_ge.le.trans hθ1
  have hθ0 : 0 < θ := lt_of_lt_of_le hS0 hθS
  have hD : 0 < (1 - r) * θ := mul_pos hapos hθ0
  have hKD : K ≤ (1 - r) * θ := by
    rw [div_le_iff₀ hapos] at hθS; linarith
  have h1 : K / ((1 - r) * θ) ≤ 1 := (div_le_one hD).mpr hKD
  have hDle : (1 - r) * θ ≤ 1 := by nlinarith
  have h2 : 1 - δ < K / ((1 - r) * θ) := by
    rw [lt_div_iff₀ hD]; nlinarith
  unfold alpha
  constructor
  · apply mul_nonneg (by positivity); linarith
  · have e : 1 / δ * (1 - K / ((1 - r) * θ)) = (1 - K / ((1 - r) * θ)) / δ := by ring
    rw [e, div_lt_one hδ0]
    linarith

variable {K δ r : ℝ}

lemma Facts.c_bounds (F : Facts K δ r) (θ : ℝ) : 0 ≤ commitProb K δ r θ ∧ commitProb K δ r θ < 1 := by
  unfold commitProb
  split_ifs with h
  · exact F.hα θ h
  · exact ⟨le_refl _, one_pos⟩

lemma Facts.c_zero (F : Facts K δ r) {θ : ℝ} (h : θ < thetaP K δ r) : commitProb K δ r θ = 0 := by
  unfold commitProb; rw [if_neg]; intro h'; linarith [h'.1]

lemma Facts.c_alpha (F : Facts K δ r) {θ : ℝ} (h1 : thetaP K δ r ≤ θ) (h2 : θ ≤ 1) :
    commitProb K δ r θ = alpha K δ θ r := by
  unfold commitProb; rw [if_pos ⟨h1, h2⟩]

lemma Facts.c_abs (F : Facts K δ r) (θ : ℝ) : |commitProb K δ r θ| ≤ 1 := by
  have := F.c_bounds θ; rw [abs_le]; constructor <;> linarith

/-- Interval integrability of `f θ * (1 - c θ)` for `f` continuous. -/
lemma Facts.ii_mul (F : Facts K δ r) {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    IntervalIntegrable (fun θ => f θ * (1 - commitProb K δ r θ)) volume a b := by
  have h1 : IntervalIntegrable (fun θ => 1 - commitProb K δ r θ) volume a b :=
    ivl_int_of_bdd (by have := meas_c K δ r; fun_prop) 1
      (fun θ => by have := F.c_bounds θ; rw [abs_le]; constructor <;> linarith) a b
  exact h1.continuousOn_mul hf.continuousOn

/-- `Φ = ∫_{θS}^1 (θ - θP)(1 - c)`; OC0 ⇔ Φ ≤ 0. -/
lemma Facts.oc0_iff (F : Facts K δ r) :
    OC0 K δ r ↔ (∫ θ in (thetaS K r)..1, (θ - thetaP K δ r) * (1 - commitProb K δ r θ)) ≤ 0 := by
  unfold OC0
  have hSP := F.hSP
  have hS1 : thetaS K r < 1 := lt_of_lt_of_le hSP F.hP1
  have iD := F.ii_mul (f := fun _ => (1:ℝ)) continuous_const (thetaS K r) 1
  have iN := F.ii_mul (f := fun θ => θ) continuous_id (thetaS K r) 1
  simp only [one_mul] at iD
  have hD : 0 < ∫ θ in (thetaS K r)..1, (1 - commitProb K δ r θ) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on iD _ hS1
    intro x _; have := F.c_bounds x; linarith
  rw [div_le_iff₀ hD]
  have e : (∫ θ in (thetaS K r)..1, (θ - thetaP K δ r) * (1 - commitProb K δ r θ)) =
      (∫ θ in (thetaS K r)..1, θ * (1 - commitProb K δ r θ)) -
        thetaP K δ r * ∫ θ in (thetaS K r)..1, (1 - commitProb K δ r θ) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub iN (iD.const_mul _)]
    congr 1; ext θ; ring
  rw [e, mul_comm]; constructor <;> intro h <;> linarith

lemma Facts.phi_split (F : Facts K δ r) :
    (∫ θ in (thetaS K r)..1, (θ - thetaP K δ r) * (1 - commitProb K δ r θ)) =
      (∫ θ in (thetaP K δ r)..1, (θ - thetaP K δ r) * (1 - alpha K δ θ r)) -
        ∫ θ in (thetaS K r)..(thetaP K δ r), (thetaP K δ r - θ) := by
  have hcont : Continuous (fun θ : ℝ => θ - thetaP K δ r) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (F.ii_mul hcont _ (thetaP K δ r))
    (F.ii_mul hcont _ _)]
  have e1 : (∫ θ in (thetaS K r)..(thetaP K δ r), (θ - thetaP K δ r) * (1 - commitProb K δ r θ))
      = -∫ θ in (thetaS K r)..(thetaP K δ r), (thetaP K δ r - θ) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le F.hSP.le] at hθ
    rcases eq_or_lt_of_le hθ.2 with h | h
    · simp [h]
    · simp only [F.c_zero h]; ring
  have e2 : (∫ θ in (thetaP K δ r)..1, (θ - thetaP K δ r) * (1 - commitProb K δ r θ))
      = ∫ θ in (thetaP K δ r)..1, (θ - thetaP K δ r) * (1 - alpha K δ θ r) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le F.hP1] at hθ
    simp only [F.c_alpha hθ.1 hθ.2]
  rw [e1, e2]; ring

lemma Facts.oc0_iff_ineq4 (F : Facts K δ r) : OC0 K δ r ↔ Ineq4 K δ r := by
  rw [F.oc0_iff, F.phi_split]; unfold Ineq4; constructor <;> intro h <;> linarith


/-- the platform's gain from entering -/
def gP (K δ r θ : ℝ) : ℝ := δ * (1 - r) * θ - K

lemma pP_eq (b θ : ℝ) : platformPayoff K δ r b θ = r * θ + b * gP K δ r θ := by
  unfold platformPayoff gP; ring

lemma inner_eq {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (β : X → ℝ) (hβ : Measurable β) (hβ01 : ∀ x, β x ∈ Set.Icc (0:ℝ) 1) (θ : ℝ) :
    ∫ x, platformPayoff K δ r (β x) θ ∂μ = r * θ + (∫ x, β x ∂μ) * gP K δ r θ := by
  simp_rw [pP_eq]
  have hi : Integrable β μ := Integrable.of_bound hβ.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun x => by
      have := hβ01 x; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]))
  rw [integral_add (integrable_const _) (hi.mul_const _), integral_const, integral_mul_const]
  simp

lemma value_eq {X : Type} [MeasurableSpace X] (σ : ℝ → Measure X) (hσ : IsInfoPolicy σ)
    (β : X → ℝ) (hβ : Measurable β) (hβ01 : ∀ x, β x ∈ Set.Icc (0:ℝ) 1) (E : Set ℝ) (a : ℝ)
    (hE : E ∩ Set.Icc (0:ℝ) 1 = Set.Icc a 1) :
    platformValue K δ r σ β E =
      ∫ θ in Set.Icc a 1, (r * θ + entryProb σ β θ * gP K δ r θ) := by
  unfold platformValue
  rw [hE]
  congr 1; ext θ
  haveI := hσ.2 θ
  rw [inner_eq (σ θ) β hβ hβ01 θ]; rfl

lemma Facts.intOn_c (F : Facts K δ r) (a b : ℝ) :
    IntegrableOn (commitProb K δ r) (Set.Icc a b) := by
  apply Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne
    (meas_c K δ r).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by simpa using F.c_abs x)

lemma Facts.split (F : Facts K δ r) (a : ℝ) (b1 b0 : ℝ) :
    (∫ θ in Set.Icc a 1, (r * θ + (commitProb K δ r θ * b1 + (1 - commitProb K δ r θ) * b0)
        * gP K δ r θ)) =
      (∫ θ in Set.Icc a 1, r * θ) + b1 * (∫ θ in Set.Icc a 1, commitProb K δ r θ * gP K δ r θ)
        + b0 * ∫ θ in Set.Icc a 1, (1 - commitProb K δ r θ) * gP K δ r θ := by
  have hg : Continuous (gP K δ r) := by unfold gP; fun_prop
  have i1 : IntegrableOn (fun θ => commitProb K δ r θ * gP K δ r θ) (Set.Icc a 1) :=
    (F.intOn_c a 1).mul_continuousOn hg.continuousOn isCompact_Icc
  have i0' : IntegrableOn (fun θ => 1 - commitProb K δ r θ) (Set.Icc a 1) :=
    (integrableOn_const (by simp)).sub (F.intOn_c a 1)
  have i0 : IntegrableOn (fun θ => (1 - commitProb K δ r θ) * gP K δ r θ) (Set.Icc a 1) :=
    i0'.mul_continuousOn hg.continuousOn isCompact_Icc
  have ir : IntegrableOn (fun θ : ℝ => r * θ) (Set.Icc a 1) :=
    (continuous_const.mul continuous_id).integrableOn_Icc
  have e : (fun θ => r * θ + (commitProb K δ r θ * b1 + (1 - commitProb K δ r θ) * b0)
        * gP K δ r θ) = fun θ => (r * θ + b1 * (commitProb K δ r θ * gP K δ r θ)) +
          b0 * ((1 - commitProb K δ r θ) * gP K δ r θ) := by ext θ; ring
  rw [e, integral_add (f := fun θ => r * θ + b1 * (commitProb K δ r θ * gP K δ r θ))
      (g := fun θ => b0 * ((1 - commitProb K δ r θ) * gP K δ r θ))
      (ir.add (i1.const_mul b1)) (i0.const_mul b0),
    integral_add (f := fun θ : ℝ => r * θ)
      (g := fun θ => b1 * (commitProb K δ r θ * gP K δ r θ)) ir (i1.const_mul b1),
    integral_const_mul b1, integral_const_mul b0]

lemma Facts.I1_nonneg (F : Facts K δ r) :
    0 ≤ ∫ θ in Set.Icc (thetaS K r) 1, commitProb K δ r θ * gP K δ r θ := by
  rw [integral_Icc_eq_integral_Ioo]
  apply setIntegral_nonneg measurableSet_Ioo
  intro θ hθ
  by_cases h : thetaP K δ r ≤ θ
  · have hP : thetaP K δ r < 1 := lt_of_le_of_lt h hθ.2
    have hlt : K < δ * (1 - r) := by
      by_contra hc; unfold thetaP at hP; rw [if_neg hc] at hP; exact lt_irrefl _ hP
    have hPe : thetaP K δ r = K / (δ * (1 - r)) := by unfold thetaP; rw [if_pos hlt]
    have hpos : 0 < δ * (1 - r) := mul_pos F.hδ0 (by linarith [F.hrK, F.hK0])
    have : 0 ≤ gP K δ r θ := by
      unfold gP; rw [hPe, div_le_iff₀ hpos] at h; nlinarith
    exact mul_nonneg (F.c_bounds θ).1 this
  · rw [F.c_zero (lt_of_not_ge h)]; simp

/-- `I0 ≤ 0 ↔ OC0`. -/
lemma Facts.I0_iff (F : Facts K δ r) :
    (∫ θ in Set.Icc (thetaS K r) 1, (1 - commitProb K δ r θ) * gP K δ r θ) ≤ 0 ↔ OC0 K δ r := by
  rw [F.oc0_iff]
  have hS1 : thetaS K r ≤ 1 := (F.hSP.trans_le F.hP1).le
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hS1]
  by_cases hlt : K < δ * (1 - r)
  · have hPe : thetaP K δ r = K / (δ * (1 - r)) := by unfold thetaP; rw [if_pos hlt]
    have hpos : 0 < δ * (1 - r) := mul_pos F.hδ0 (by linarith [F.hrK, F.hK0])
    have e : (∫ θ in (thetaS K r)..1, (1 - commitProb K δ r θ) * gP K δ r θ) =
        (δ * (1 - r)) * ∫ θ in (thetaS K r)..1, (θ - thetaP K δ r) * (1 - commitProb K δ r θ) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; ext θ; unfold gP; rw [hPe]
      have hq : δ * (1 - r) * (K / (δ * (1 - r))) = K := mul_div_cancel₀ _ hpos.ne'
      linear_combination (1 - commitProb K δ r θ) * hq
    rw [e]
    constructor
    · intro h; by_contra hc; push_neg at hc; nlinarith
    · intro h; nlinarith
  · have hP : thetaP K δ r = 1 := by unfold thetaP; rw [if_neg hlt]
    have hδr : δ * (1 - r) ≤ K := not_lt.mp hlt
    constructor
    · intro _
      have := intervalIntegral.integral_nonneg (μ := volume) hS1
        (f := fun θ => -((θ - thetaP K δ r) * (1 - commitProb K δ r θ))) (fun θ hθ => by
          rw [hP]; simp only [neg_nonneg]
          exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hθ.2]) (by linarith [(F.c_bounds θ).2]))
      rw [intervalIntegral.integral_neg] at this; linarith
    · intro _
      have := intervalIntegral.integral_nonneg (μ := volume) hS1
        (f := fun θ => -((1 - commitProb K δ r θ) * gP K δ r θ)) (fun θ hθ => by
      simp only [neg_nonneg]
      have h0 : 0 ≤ 1 - commitProb K δ r θ := by linarith [(F.c_bounds θ).2]
      have : gP K δ r θ ≤ 0 := by
        unfold gP
        have : 0 ≤ δ * (1 - r) := (mul_pos F.hδ0 (by linarith [F.hrK, F.hK0])).le
        nlinarith [hθ.2, hθ.1, F.hS0]
      exact mul_nonpos_of_nonneg_of_nonpos h0 this)
      rw [intervalIntegral.integral_neg] at this; linarith

/-! signal (3) -/

lemma Facts.int_signal3 (F : Facts K δ r) (f : Bool → ℝ) (θ : ℝ) :
    ∫ x, f x ∂(signal3 K δ r θ) =
      commitProb K δ r θ * f true + (1 - commitProb K δ r θ) * f false := by
  have h0 := (F.c_bounds θ).1
  have h1 : 0 ≤ 1 - commitProb K δ r θ := by linarith [(F.c_bounds θ).2]
  haveI : IsFiniteMeasure (ENNReal.ofReal (commitProb K δ r θ) • Measure.dirac true) :=
    ⟨by simp [ENNReal.ofReal_lt_top]⟩
  haveI : IsFiniteMeasure (ENNReal.ofReal (1 - commitProb K δ r θ) • Measure.dirac false) :=
    ⟨by simp [ENNReal.ofReal_lt_top]⟩
  unfold signal3
  rw [integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal h1, smul_eq_mul, smul_eq_mul]

lemma Facts.signal3_info (F : Facts K δ r) : IsInfoPolicy (signal3 K δ r) := by
  refine ⟨?_, fun θ => ⟨?_⟩⟩
  · refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    simp only [signal3, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact ((ENNReal.measurable_ofReal.comp (meas_c K δ r)).mul_const _).add
      ((ENNReal.measurable_ofReal.comp ((meas_c K δ r).const_sub 1)).mul_const _)
  · have h0 := (F.c_bounds θ).1
    have h1 : 0 ≤ 1 - commitProb K δ r θ := by linarith [(F.c_bounds θ).2]
    simp only [signal3, Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    rw [← ENNReal.ofReal_add h0 h1]; simp

lemma Facts.entry_signal3 (F : Facts K δ r) (θ : ℝ) :
    entryProb (signal3 K δ r) recommend θ = commitProb K δ r θ := by
  unfold entryProb; rw [F.int_signal3]; simp [recommend]

lemma Facts.E_inter (F : Facts K δ r) :
    Set.Icc (thetaS K r) 1 ∩ Set.Icc (0:ℝ) 1 = Set.Icc (thetaS K r) 1 :=
  Set.inter_eq_left.mpr (Set.Icc_subset_Icc F.hS0.le le_rfl)

lemma Facts.implements (F : Facts K δ r) :
    ImplementsCommitment K δ r (signal3 K δ r) recommend (Set.Icc (thetaS K r) 1) :=
  ⟨F.E_inter, fun θ _ => F.entry_signal3 θ⟩

lemma Facts.seller_ok (F : Facts K δ r) :
    (∀ θ ∈ Set.Icc (0:ℝ) 1, θ ∈ Set.Icc (thetaS K r) 1 →
      0 ≤ sellerGain K δ r (commitProb K δ r θ) θ) ∧
    (∀ θ ∈ Set.Icc (0:ℝ) 1, θ ∉ Set.Icc (thetaS K r) 1 →
      sellerGain K δ r (commitProb K δ r θ) θ ≤ 0) := by
  have hapos : 0 < 1 - r := by linarith [F.hrK, F.hK0]
  have hS := F.hS
  constructor
  · intro θ _ hθ
    have hθS : K / (1 - r) ≤ θ := hS ▸ hθ.1
    have hθ0 : 0 < θ := lt_of_lt_of_le (div_pos F.hK0 hapos) hθS
    by_cases h : thetaP K δ r ≤ θ
    · rw [F.c_alpha h hθ.2]
      unfold sellerGain alpha
      have := F.hδ0.ne'; have := hθ0.ne'; have := hapos.ne'
      have : ((1 - δ) + δ * (1 - 1 / δ * (1 - K / ((1 - r) * θ)))) * (1 - r) * θ - K = 0 := by
        field_simp; ring
      rw [this]
    · rw [F.c_zero (lt_of_not_ge h)]
      unfold sellerGain
      rw [div_le_iff₀ hapos] at hθS; nlinarith
  · intro θ hθ01 hθ
    have hlt : θ < thetaS K r := by
      by_contra hc; exact hθ ⟨not_lt.mp hc, hθ01.2⟩
    rw [F.c_zero (hlt.trans F.hSP)]
    unfold sellerGain
    rw [hS, lt_div_iff₀ hapos] at hlt; nlinarith

lemma Facts.value_signal3 (F : Facts K δ r) (β : Bool → ℝ) (hβ01 : ∀ x, β x ∈ Set.Icc (0:ℝ) 1) :
    platformValue K δ r (signal3 K δ r) β (Set.Icc (thetaS K r) 1) =
      (∫ θ in Set.Icc (thetaS K r) 1, r * θ) +
        β true * (∫ θ in Set.Icc (thetaS K r) 1, commitProb K δ r θ * gP K δ r θ)
        + β false * ∫ θ in Set.Icc (thetaS K r) 1, (1 - commitProb K δ r θ) * gP K δ r θ := by
  rw [value_eq _ F.signal3_info β (measurable_of_finite β) hβ01 _ _ F.E_inter, ← F.split]
  congr 1; ext θ
  unfold entryProb; rw [F.int_signal3] <;> ring

lemma Facts.signal3_eq_iff (F : Facts K δ r) :
    IsEquilibrium K δ r (signal3 K δ r) recommend (Set.Icc (thetaS K r) 1) ↔ OC0 K δ r := by
  rw [← F.I0_iff]
  have hI1 := F.I1_nonneg
  have hrec : ∀ x, recommend x ∈ Set.Icc (0:ℝ) 1 := by
    intro x; cases x <;> simp [recommend]
  constructor
  · intro h
    have := h.platform_opt (fun _ => 1) measurable_const (fun _ => ⟨zero_le_one, le_rfl⟩)
    rw [F.value_signal3 _ (fun _ => ⟨zero_le_one, le_rfl⟩), F.value_signal3 _ hrec] at this
    simp [recommend] at this
    linarith
  · intro h
    obtain ⟨s1, s2⟩ := F.seller_ok
    refine ⟨fun θ h1 h2 => ?_, fun θ h1 h2 => ?_, ?_⟩
    · rw [F.entry_signal3]; exact s1 θ h1 h2
    · rw [F.entry_signal3]; exact s2 θ h1 h2
    · intro β' _ hβ'
      rw [F.value_signal3 _ hβ', F.value_signal3 _ hrec]
      simp only [recommend]
      have a1 := hβ' true; have a0 := hβ' false
      simp only [Set.mem_Icc] at a1 a0
      have : β' true * (∫ θ in Set.Icc (thetaS K r) 1, commitProb K δ r θ * gP K δ r θ) ≤
          (∫ θ in Set.Icc (thetaS K r) 1, commitProb K δ r θ * gP K δ r θ) := by
        nlinarith
      have : β' false * (∫ θ in Set.Icc (thetaS K r) 1, (1 - commitProb K δ r θ) * gP K δ r θ)
          ≤ 0 := by nlinarith
      simp; linarith

lemma Facts.oc1 (F : Facts K δ r) (hP : thetaP K δ r < 1) : OC1 K δ r := by
  unfold OC1
  have hlt : K < δ * (1 - r) := by
    by_contra hc; unfold thetaP at hP; rw [if_neg hc] at hP; exact lt_irrefl _ hP
  have hapos : 0 < 1 - r := by linarith [F.hrK, F.hK0]
  have hS1 : thetaS K r ≤ 1 := (F.hSP.trans_le F.hP1).le
  -- c > 0 on (θP, 1]
  have cpos : ∀ θ ∈ Set.Ioo (thetaP K δ r) 1, 0 < commitProb K δ r θ := by
    intro θ hθ
    rw [F.c_alpha hθ.1.le hθ.2.le]
    have hθS : K / (1 - r) < θ := F.hS ▸ (F.hSP.trans hθ.1)
    have hθ0 : 0 < θ := lt_trans (div_pos F.hK0 hapos) hθS
    unfold alpha
    apply mul_pos (by have := F.hδ0; positivity)
    rw [sub_pos, div_lt_one (by positivity)]
    rw [div_lt_iff₀ hapos] at hθS; linarith
  have iC : ∀ a b, IntervalIntegrable (commitProb K δ r) volume a b := fun a b =>
    ivl_int_of_bdd (meas_c K δ r) 1 F.c_abs a b
  have iCθ : ∀ a b, IntervalIntegrable (fun θ => (θ - thetaP K δ r) * commitProb K δ r θ)
      volume a b := fun a b => (iC a b).continuousOn_mul (by fun_prop)
  have iCid : ∀ a b, IntervalIntegrable (fun θ => θ * commitProb K δ r θ) volume a b :=
    fun a b => (iC a b).continuousOn_mul (by fun_prop)
  have hD : 0 < ∫ θ in (thetaS K r)..1, commitProb K δ r θ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (iC _ (thetaP K δ r)) (iC _ _)]
    have a1 : 0 ≤ ∫ θ in (thetaS K r)..(thetaP K δ r), commitProb K δ r θ :=
      intervalIntegral.integral_nonneg F.hSP.le (fun θ _ => (F.c_bounds θ).1)
    have a2 : 0 < ∫ θ in (thetaP K δ r)..1, commitProb K δ r θ :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (iC _ _) cpos hP
    linarith
  rw [lt_div_iff₀ hD]
  have hN : 0 < ∫ θ in (thetaS K r)..1, (θ - thetaP K δ r) * commitProb K δ r θ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (iCθ _ (thetaP K δ r)) (iCθ _ _)]
    have a1 : (∫ θ in (thetaS K r)..(thetaP K δ r), (θ - thetaP K δ r) * commitProb K δ r θ) = 0 := by
      rw [← intervalIntegral.integral_zero (a := thetaS K r) (b := thetaP K δ r)]
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [Set.uIcc_of_le F.hSP.le] at hθ
      rcases eq_or_lt_of_le hθ.2 with h | h
      · simp [h]
      · simp [F.c_zero h]
    have a2 : 0 < ∫ θ in (thetaP K δ r)..1, (θ - thetaP K δ r) * commitProb K δ r θ :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (iCθ _ _)
        (fun θ hθ => mul_pos (by linarith [hθ.1]) (cpos θ hθ)) hP
    linarith
  have e : (∫ θ in (thetaS K r)..1, (θ - thetaP K δ r) * commitProb K δ r θ) =
      (∫ θ in (thetaS K r)..1, θ * commitProb K δ r θ) -
        thetaP K δ r * ∫ θ in (thetaS K r)..1, commitProb K δ r θ := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (iCid _ _)
      ((iC _ _).const_mul _)]
    congr 1; ext θ; ring
  rw [e] at hN; linarith

lemma Facts.signal3_obedience (F : Facts K δ r) :
    IsInfoPolicy (signal3 K δ r) ∧
      ImplementsCommitment K δ r (signal3 K δ r) recommend (Set.Icc (thetaS K r) 1) ∧
      (IsEquilibrium K δ r (signal3 K δ r) recommend (Set.Icc (thetaS K r) 1) ↔ OC0 K δ r) ∧
      (thetaP K δ r < 1 → OC1 K δ r) :=
  ⟨F.signal3_info, F.implements, F.signal3_eq_iff, F.oc1⟩

end SherlockAux

namespace SherlockAux

variable {K δ r : ℝ}

lemma PiC_zero (hδ0 : 0 < δ) (hδ1 : δ < 1) (h1 : 1 - K ≤ r) (h2 : r ≤ 1) : PiC K δ r = 0 := by
  have hS : thetaS K r = 1 := by unfold thetaS; rw [if_neg (by linarith)]
  have hP : thetaP K δ r = 1 := by
    unfold thetaP; rw [if_neg]; push_neg
    have : δ * (1 - r) ≤ 1 - r := by nlinarith
    linarith
  unfold PiC; rw [hS, hP]; simp

lemma Facts.PiC_pos (F : Facts K δ r) (hr : 0 < r) : 0 < PiC K δ r := by
  have hapos : 0 < 1 - r := by linarith [F.hrK, F.hK0]
  have hS0 := F.hS0
  have hcr : Continuous (fun θ : ℝ => r * θ) := by fun_prop
  have hmono : (∫ θ in (thetaP K δ r)..1, r * θ) ≤ ∫ θ in (thetaP K δ r)..1,
      ((1 - δ) * r * θ + (alpha K δ θ r * (δ * θ - K) + (1 - alpha K δ θ r) * (δ * r * θ))) := by
    rcases eq_or_lt_of_le F.hP1 with hP | hP
    · rw [hP]; simp
    · have hlt : K < δ * (1 - r) := by
        by_contra hc; unfold thetaP at hP; rw [if_neg hc] at hP; exact lt_irrefl _ hP
      have hPe : thetaP K δ r = K / (δ * (1 - r)) := by unfold thetaP; rw [if_pos hlt]
      have hpos : 0 < δ * (1 - r) := mul_pos F.hδ0 hapos
      have hP0 : 0 < thetaP K δ r := hS0.trans F.hSP
      apply intervalIntegral.integral_mono_on hP.le (hcr.intervalIntegrable _ _)
      · apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hP.le]
        have : ∀ θ ∈ Set.Icc (thetaP K δ r) (1:ℝ), (1 - r) * θ ≠ 0 := fun θ hθ =>
          (mul_pos hapos (lt_of_lt_of_le hP0 hθ.1)).ne'
        unfold alpha
        apply ContinuousOn.add (by fun_prop)
        apply ContinuousOn.add
        · apply ContinuousOn.mul _ (by fun_prop)
          apply ContinuousOn.mul continuousOn_const
          apply ContinuousOn.sub continuousOn_const
          exact ContinuousOn.div continuousOn_const (by fun_prop) this
        · apply ContinuousOn.mul _ (by fun_prop)
          apply ContinuousOn.sub continuousOn_const
          apply ContinuousOn.mul continuousOn_const
          apply ContinuousOn.sub continuousOn_const
          exact ContinuousOn.div continuousOn_const (by fun_prop) this
      · intro θ hθ
        have ha := (F.hα θ hθ).1
        have hg : 0 ≤ δ * (1 - r) * θ - K := by
          have := hθ.1; rw [hPe, div_le_iff₀ hpos] at this; nlinarith
        have : (1 - δ) * r * θ + (alpha K δ θ r * (δ * θ - K) +
            (1 - alpha K δ θ r) * (δ * r * θ)) - r * θ =
            alpha K δ θ r * (δ * (1 - r) * θ - K) := by ring
        nlinarith [mul_nonneg ha hg]
  have hsum : (∫ θ in (thetaS K r)..(thetaP K δ r), r * θ) + (∫ θ in (thetaP K δ r)..1, r * θ)
      = ∫ θ in (thetaS K r)..1, r * θ :=
    intervalIntegral.integral_add_adjacent_intervals (hcr.intervalIntegrable _ _)
      (hcr.intervalIntegrable _ _)
  have hpos : 0 < ∫ θ in (thetaS K r)..1, r * θ := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hcr.intervalIntegrable _ _) _
      (F.hSP.trans_le F.hP1)
    intro θ hθ; exact mul_pos hr (hS0.trans hθ.1)
  unfold PiC; linarith

lemma rC_lt (K δ rC : ℝ) (hδ1 : δ < 1) (hK1 : 1 - δ < K) (hK2 : K < δ)
    (hrC : rC ∈ Set.Icc (0:ℝ) 1) (hmax : IsMaxOn (PiC K δ) (Set.Icc (0:ℝ) 1) rC) : rC < 1 - K := by
  by_contra hc
  push_neg at hc
  have h0 : PiC K δ rC = 0 := PiC_zero (by linarith) hδ1 hc hrC.2
  set r0 := (1 - K) / 2 with hr0
  have F0 := facts K δ r0 hδ1 hK1 hK2 (by rw [hr0]; linarith) (by rw [hr0]; linarith)
  have hpos := F0.PiC_pos (by rw [hr0]; linarith)
  have := isMaxOn_iff.mp hmax r0 ⟨by rw [hr0]; linarith, by rw [hr0]; linarith⟩
  linarith

lemma Facts.necessity (F : Facts K δ r) : CommitmentImplementable K δ r → OC0 K δ r := by
  rintro ⟨X, mX, σ, β, E, hσ, hβ, hβ01, hE, heq, himp⟩
  have one01 : ∀ _ : X, (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := fun _ => ⟨zero_le_one, le_rfl⟩
  have v := heq.platform_opt (fun _ => 1) measurable_const one01
  rw [value_eq σ hσ (fun _ => 1) measurable_const one01 E _ himp.1,
    value_eq σ hσ β hβ hβ01 E _ himp.1] at v
  have e1 : (∫ θ in Set.Icc (thetaS K r) 1, (r * θ + entryProb σ (fun _ => (1:ℝ)) θ * gP K δ r θ))
      = ∫ θ in Set.Icc (thetaS K r) 1, (r * θ + (commitProb K δ r θ * 1 +
          (1 - commitProb K δ r θ) * 1) * gP K δ r θ) := by
    congr 1; ext θ
    haveI := hσ.2 θ
    simp only [entryProb, integral_const, smul_eq_mul, mul_one, probReal_univ]
    ring
  have e2 : (∫ θ in Set.Icc (thetaS K r) 1, (r * θ + entryProb σ β θ * gP K δ r θ))
      = ∫ θ in Set.Icc (thetaS K r) 1, (r * θ + (commitProb K δ r θ * 1 +
          (1 - commitProb K δ r θ) * 0) * gP K δ r θ) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro θ hθ
    simp only
    rw [himp.2 θ hθ]; ring
  rw [e1, e2, F.split, F.split] at v
  rw [← F.I0_iff]; linarith

end SherlockAux

open SherlockAux in
theorem solution (K δ rC : ℝ) (hδ1 : δ < 1) (hK1 : 1 - δ < K) (hK2 : K < δ)
    (hrC : rC ∈ Set.Icc (0:ℝ) 1) (hmax : IsMaxOn (PiC K δ) (Set.Icc (0:ℝ) 1) rC) :
    (CommitmentImplementable K δ rC ↔ OC0 K δ rC) ∧ (OC0 K δ rC ↔ Ineq4 K δ rC) := by
  have hrK := rC_lt K δ rC hδ1 hK1 hK2 hrC hmax
  have F := facts K δ rC hδ1 hK1 hK2 hrC.1 hrK
  obtain ⟨hinfo, himp, heqv, _⟩ := signal3_obedience K δ rC hδ1 hK1 hK2 hrC.1 hrK
  refine ⟨⟨F.necessity, fun h => ?_⟩, oc0_iff_ineq4 K δ rC hδ1 hK1 hK2 hrC.1 hrK⟩
  refine ⟨Bool, inferInstance, signal3 K δ rC, recommend, Set.Icc (thetaS K rC) 1, hinfo,
    measurable_of_finite _, ?_, measurableSet_Icc, heqv.mpr h, himp⟩
  intro x; cases x <;> simp [recommend]
