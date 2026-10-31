-- Prove2me | solution 1 for Sherlocking.InfoPolicy.optimal_commitment
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:34:52.390472+00:00
-- url     : https://prove2.me/submissions/f95f4189-8947-42c6-88ac-536c0a389374

import Mathlib
import Definitions.Def_Sherlocking_InfoPolicy_Model

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


def gP (K δ r θ : ℝ) : ℝ := δ * (1 - r) * θ - K

/-- the entry set Θ_E(a) -/
def ThE (K δ r : ℝ) (a : ℝ → ℝ) : Set ℝ :=
  {θ : ℝ | θ ∈ Set.Icc (0:ℝ) 1 ∧ K ≤ ((1 - δ) + δ * (1 - a θ)) * (1 - r) * θ}

lemma payoff_eq (a : ℝ → ℝ) (θ : ℝ) :
    ((1 - a θ) * r * θ + a θ * ((1 - δ) * r * θ + δ * θ - K)) = r * θ + a θ * gP K δ r θ := by
  unfold gP; ring

lemma commitPayoff_eq (a : ℝ → ℝ) : commitPayoff K δ r a = ∫ θ in ThE K δ r a, (r * θ + a θ * gP K δ r θ) := by
  unfold commitPayoff ThE; simp_rw [payoff_eq]

lemma ThE_meas (a : ℝ → ℝ) (ha : Measurable a) : MeasurableSet (ThE K δ r a) := by
  unfold ThE
  have hm : Measurable (fun θ => ((1 - δ) + δ * (1 - a θ)) * (1 - r) * θ) := by fun_prop
  exact measurableSet_Icc.inter (measurableSet_le measurable_const hm)

lemma int_zero_of_sub1 {s : Set ℝ} (f : ℝ → ℝ) (h : ∀ θ ∈ s, θ = 1) : ∫ θ in s, f θ = 0 := by
  have : volume s = 0 := measure_mono_null (fun θ hθ => by simp [h θ hθ]) (measure_singleton 1)
  rw [Measure.restrict_eq_zero.mpr this, integral_zero_measure]

lemma ae_ne (a : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a := by
  rw [ae_iff]; simp

lemma Facts.ThE_c (F : Facts K δ r) : ThE K δ r (commitProb K δ r) = Set.Icc (thetaS K r) 1 := by
  have hapos : 0 < 1 - r := by linarith [F.hrK, F.hK0]
  ext θ
  simp only [ThE, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h0, h1⟩, hK⟩
    refine ⟨?_, h1⟩
    by_contra hc; push_neg at hc
    rw [F.c_zero (hc.trans F.hSP)] at hK
    rw [F.hS, lt_div_iff₀ hapos] at hc; nlinarith
  · rintro ⟨h0, h1⟩
    have hθ0 : 0 < θ := F.hS0.trans_le h0
    refine ⟨⟨hθ0.le, h1⟩, ?_⟩
    by_cases h : thetaP K δ r ≤ θ
    · rw [F.c_alpha h h1]; unfold alpha
      have := F.hδ0.ne'; have := hθ0.ne'; have := hapos.ne'
      apply le_of_eq; field_simp; ring
    · rw [F.c_zero (lt_of_not_ge h)]
      rw [F.hS, div_le_iff₀ hapos] at h0; nlinarith

lemma Facts.int_v (F : Facts K δ r) :
    (∫ θ in Set.Icc (thetaS K r) 1, (r * θ + commitProb K δ r θ * gP K δ r θ)) = PiC K δ r := by
  have hS1 : thetaS K r ≤ 1 := (F.hSP.trans_le F.hP1).le
  have hg : Continuous (gP K δ r) := by unfold gP; fun_prop
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hS1]
  have ii : ∀ a b, IntervalIntegrable (fun θ => r * θ + commitProb K δ r θ * gP K δ r θ)
      volume a b := fun a b =>
    (continuous_const.mul continuous_id).intervalIntegrable a b |>.add
      ((ivl_int_of_bdd (meas_c K δ r) 1 F.c_abs a b).mul_continuousOn hg.continuousOn)
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii _ (thetaP K δ r)) (ii _ _)]
  unfold PiC
  congr 1
  · apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_ne (thetaP K δ r)] with θ hne hθ
    rw [Set.uIoc_of_le F.hSP.le] at hθ
    rw [F.c_zero (lt_of_le_of_ne hθ.2 hne)]; ring
  · apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le F.hP1] at hθ
    simp only [F.c_alpha hθ.1 hθ.2]
    unfold gP; ring

lemma Facts.upper (F : Facts K δ r) (a : ℝ → ℝ) (ha : Measurable a)
    (ha01 : ∀ θ, a θ ∈ Set.Icc (0:ℝ) 1) : commitPayoff K δ r a ≤ PiC K δ r := by
  have hapos : 0 < 1 - r := by linarith [F.hrK, F.hK0]
  have hg : Continuous (gP K δ r) := by unfold gP; fun_prop
  have hS1 : thetaS K r ≤ 1 := (F.hSP.trans_le F.hP1).le
  rw [commitPayoff_eq]
  have hmeas := ThE_meas (K := K) (δ := δ) (r := r) a ha
  -- Θ_E(a) ⊆ [θS, 1], and on it a θ ≤ α θ when θ ≥ θP
  have hsub : ∀ θ ∈ ThE K δ r a, θ ∈ Set.Icc (thetaS K r) 1 ∧
      (thetaP K δ r ≤ θ → a θ ≤ alpha K δ θ r) := by
    rintro θ ⟨⟨h0, h1⟩, hK⟩
    have ha0 := (ha01 θ).1; have ha1 := (ha01 θ).2
    have hδ0 := F.hδ0
    have hle : ((1 - δ) + δ * (1 - a θ)) ≤ 1 := by nlinarith
    have hKle : K ≤ (1 - r) * θ := by
      have : ((1 - δ) + δ * (1 - a θ)) * ((1 - r) * θ) ≤ 1 * ((1 - r) * θ) :=
        mul_le_mul_of_nonneg_right hle (mul_nonneg hapos.le h0)
      nlinarith
    have hθ0 : 0 < θ := by
      by_contra hc; push_neg at hc
      have : θ = 0 := le_antisymm hc h0
      subst this; nlinarith [F.hK0]
    refine ⟨⟨by rw [F.hS, div_le_iff₀ hapos]; linarith, h1⟩, fun _ => ?_⟩
    unfold alpha
    have hpos : 0 < (1 - r) * θ := mul_pos hapos hθ0
    have : K / ((1 - r) * θ) ≤ 1 - δ * a θ := by
      rw [div_le_iff₀ hpos]; nlinarith
    have e : 1 / δ * (1 - K / ((1 - r) * θ)) = (1 - K / ((1 - r) * θ)) / δ := by ring
    rw [e, le_div_iff₀ hδ0]; linarith
  have hsubset : ThE K δ r a ⊆ Set.Icc (thetaS K r) 1 := fun θ h => (hsub θ h).1
  have iaS : IntegrableOn (fun θ => r * θ + a θ * gP K δ r θ) (ThE K δ r a) := by
    have iA : IntegrableOn a (Set.Icc (0:ℝ) 1) := by
      apply Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne ha.aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun x => by
        have := ha01 x; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2])
    exact (((continuous_const.mul continuous_id).integrableOn_Icc).add
      (iA.mul_continuousOn hg.continuousOn isCompact_Icc)).mono_set (fun θ h => h.1)
  rcases eq_or_lt_of_le F.hP1 with hP | hP
  · -- θP = 1: g ≤ 0 on [0,1]
    have hδr : δ * (1 - r) ≤ K := by
      by_contra hc; push_neg at hc
      have : thetaP K δ r = K / (δ * (1 - r)) := by unfold thetaP; rw [if_pos hc]
      rw [this, div_eq_one_iff_eq (mul_pos F.hδ0 hapos).ne'] at hP; linarith
    have hPiC : PiC K δ r = ∫ θ in Set.Icc (thetaS K r) 1, r * θ := by
      unfold PiC; rw [hP, intervalIntegral.integral_same, add_zero,
        intervalIntegral.integral_of_le hS1, integral_Icc_eq_integral_Ioc]
    rw [hPiC]
    have ir : IntegrableOn (fun θ : ℝ => r * θ) (ThE K δ r a) :=
      ((continuous_const.mul continuous_id).integrableOn_Icc).mono_set hsubset
    calc (∫ θ in ThE K δ r a, (r * θ + a θ * gP K δ r θ))
        ≤ ∫ θ in ThE K δ r a, r * θ := by
          apply setIntegral_mono_on iaS ir hmeas
          intro θ hθ
          have h1 := (hsub θ hθ).1.2
          have : gP K δ r θ ≤ 0 := by
            unfold gP; nlinarith [(mul_pos F.hδ0 hapos).le, (hsub θ hθ).1.1, F.hS0]
          nlinarith [(ha01 θ).1]
      _ ≤ ∫ θ in Set.Icc (thetaS K r) 1, r * θ := by
          apply setIntegral_mono_set ((continuous_const.mul continuous_id).integrableOn_Icc)
          · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
            exact Filter.Eventually.of_forall (fun θ hθ => mul_nonneg F.hr0 (F.hS0.le.trans hθ.1))
          · exact Filter.Eventually.of_forall hsubset
  · have hlt : K < δ * (1 - r) := by
      by_contra hc; unfold thetaP at hP; rw [if_neg hc] at hP; exact lt_irrefl _ hP
    have hPe : thetaP K δ r = K / (δ * (1 - r)) := by unfold thetaP; rw [if_pos hlt]
    have hpos : 0 < δ * (1 - r) := mul_pos F.hδ0 hapos
    have gnn : ∀ θ, thetaP K δ r ≤ θ → 0 ≤ gP K δ r θ := by
      intro θ h; unfold gP; rw [hPe, div_le_iff₀ hpos] at h; nlinarith
    have gnp : ∀ θ, θ < thetaP K δ r → gP K δ r θ ≤ 0 := by
      intro θ h; unfold gP; rw [hPe, lt_div_iff₀ hpos] at h; nlinarith
    have iv : IntegrableOn (fun θ => r * θ + commitProb K δ r θ * gP K δ r θ)
        (Set.Icc (thetaS K r) 1) := by
      have iC : IntegrableOn (commitProb K δ r) (Set.Icc (thetaS K r) 1) := by
        apply Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne
          (meas_c K δ r).aestronglyMeasurable
        exact Filter.Eventually.of_forall (fun x => by simpa using F.c_abs x)
      exact ((continuous_const.mul continuous_id).integrableOn_Icc).add
        (iC.mul_continuousOn hg.continuousOn isCompact_Icc)
    rw [← F.int_v]
    calc (∫ θ in ThE K δ r a, (r * θ + a θ * gP K δ r θ))
        ≤ ∫ θ in ThE K δ r a, (r * θ + commitProb K δ r θ * gP K δ r θ) := by
          apply setIntegral_mono_on iaS (iv.mono_set hsubset) hmeas
          intro θ hθ
          obtain ⟨⟨h0, h1⟩, hα⟩ := hsub θ hθ
          by_cases h : thetaP K δ r ≤ θ
          · rw [F.c_alpha h h1]
            nlinarith [hα h, gnn θ h]
          · rw [F.c_zero (lt_of_not_ge h)]
            nlinarith [gnp θ (lt_of_not_ge h), (ha01 θ).1]
      _ ≤ ∫ θ in Set.Icc (thetaS K r) 1, (r * θ + commitProb K δ r θ * gP K δ r θ) := by
          apply setIntegral_mono_set iv
          · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
            refine Filter.Eventually.of_forall (fun θ hθ => ?_)
            have : 0 ≤ commitProb K δ r θ * gP K δ r θ := by
              by_cases h : thetaP K δ r ≤ θ
              · exact mul_nonneg (F.c_bounds θ).1 (gnn θ h)
              · rw [F.c_zero (lt_of_not_ge h)]; simp
            have : 0 ≤ r * θ := mul_nonneg F.hr0 (F.hS0.le.trans hθ.1)
            simp only [Pi.zero_apply]; linarith
          · exact Filter.Eventually.of_forall hsubset

end SherlockAux

open SherlockAux in
theorem solution (K δ r : ℝ) (hδ1 : δ < 1) (hK1 : 1 - δ < K) (hK2 : K < δ) (hr0 : 0 ≤ r)
    (hr1 : r < 1) : commitPayoff K δ r (commitProb K δ r) = PiC K δ r ∧
      (∀ a : ℝ → ℝ, Measurable a → (∀ θ, a θ ∈ Set.Icc (0:ℝ) 1) → commitPayoff K δ r a ≤ PiC K δ r) ∧
      (r < 1 - K → Measurable (commitProb K δ r) ∧ ∀ θ, commitProb K δ r θ ∈ Set.Icc (0:ℝ) 1) := by
  have hδ0 : 0 < δ := by linarith
  have hK0 : 0 < K := by linarith
  have hapos : 0 < 1 - r := by linarith
  by_cases hrK : r < 1 - K
  · have F := facts K δ r hδ1 hK1 hK2 hr0 hrK
    refine ⟨?_, F.upper, fun _ => ⟨meas_c K δ r, fun θ => ⟨(F.c_bounds θ).1, (F.c_bounds θ).2.le⟩⟩⟩
    rw [commitPayoff_eq, F.ThE_c, F.int_v]
  · push_neg at hrK
    have hPiC : PiC K δ r = 0 := by
      have hS : thetaS K r = 1 := by unfold thetaS; rw [if_neg (by linarith)]
      have hP : thetaP K δ r = 1 := by
        unfold thetaP; rw [if_neg]; push_neg
        have : δ * (1 - r) ≤ 1 - r := by nlinarith
        linarith
      unfold PiC; rw [hS, hP]; simp
    refine ⟨?_, ?_, fun h => absurd h (not_lt.mpr hrK)⟩
    · rw [hPiC, commitPayoff_eq]
      apply int_zero_of_sub1
      rintro θ ⟨⟨h0, h1⟩, hK⟩
      by_contra hne
      have hθ1 : θ < 1 := lt_of_le_of_ne h1 hne
      have hP : thetaP K δ r = 1 := by
        unfold thetaP; rw [if_neg]; push_neg
        have : δ * (1 - r) ≤ 1 - r := by nlinarith
        linarith
      have hc : commitProb K δ r θ = 0 := by
        unfold commitProb; rw [if_neg]; rintro ⟨h, _⟩; rw [hP] at h; linarith
      rw [hc] at hK
      nlinarith
    · intro a ha ha01
      rw [hPiC, commitPayoff_eq, int_zero_of_sub1]
      rintro θ ⟨⟨h0, h1⟩, hK⟩
      by_contra hne
      have hθ1 : θ < 1 := lt_of_le_of_ne h1 hne
      have ha0 := (ha01 θ).1; have ha1 := (ha01 θ).2
      have hle : ((1 - δ) + δ * (1 - a θ)) ≤ 1 := by nlinarith
      have : ((1 - δ) + δ * (1 - a θ)) * ((1 - r) * θ) ≤ 1 * ((1 - r) * θ) :=
        mul_le_mul_of_nonneg_right hle (mul_nonneg hapos.le h0)
      nlinarith
