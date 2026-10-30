-- Prove2me | solution 1 for SideConstrainedDTA.Existence.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:52:32.129296+00:00
-- url     : https://prove2.me/submissions/f4e887f1-bfcc-428c-8919-5b0fcb1e369e

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting

open MeasureTheory Set Filter Topology

namespace SideConstrainedDTA.Existence.Sol33

open SideConstrainedDTA.Existence

variable {I W E : Type*} [Fintype W] [DecidableEq I] [DecidableEq W]

lemma lam_bd (N : Model I W E) {h : W → ℝ → ℝ} (hh : Lam N h) (p : W) :
    ∀ᵐ t ∂(volume.restrict (Icc N.t0 N.tf)), 0 ≤ h p t ∧ h p t ≤ N.B p := by
  have h1 := ae_restrict_of_ae (μ := volume) (s := Icc N.t0 N.tf) (hh.2.1 p)
  filter_upwards [h1, ae_restrict_mem measurableSet_Icc] with t ht htI
  exact (ht.1 htI)

lemma lam_int (N : Model I W E) {h : W → ℝ → ℝ} (hh : Lam N h) (p : W) :
    Integrable (h p) (volume.restrict (Icc N.t0 N.tf)) :=
  Integrable.of_bound (hh.1 p).aestronglyMeasurable (N.B p) (by
    filter_upwards [lam_bd N hh p] with t ht
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [ht.1, ht.2])

/-- The mass-transfer argument: moving a little mass from walk `p` on `S1`, where `Φ_p > α`,
to walk `q` on `S2`, where `Φ_q ≤ β < α`, makes the variational inequality fail. -/
lemma transfer (N : Model I W E) (Φ : (W → ℝ → ℝ) → W → ℝ → ℝ) (hs : W → ℝ → ℝ)
    (hhs : Lam N hs) (Φ' : W → ℝ → ℝ) (hΦ'm : ∀ w, Measurable (Φ' w))
    (hΦ'ae : ∀ w, Φ hs w =ᵐ[volume.restrict (Icc N.t0 N.tf)] Φ' w) (K : ℝ)
    (hK : ∀ w, ∀ᵐ t ∂(volume.restrict (Icc N.t0 N.tf)), |Φ' w t| ≤ K)
    (hvi : ∀ h, Lam N h → 0 ≤ ∑ p, ∫ t in Icc N.t0 N.tf, Φ hs p t * (h p t - hs p t))
    (p q : W) (hpq : N.com p = N.com q) (S1 S2 : Set ℝ) (hS1m : MeasurableSet S1)
    (hS2m : MeasurableSet S2) (hS1I : S1 ⊆ Icc N.t0 N.tf) (hS2I : S2 ⊆ Icc N.t0 N.tf)
    (hS1pos : 0 < volume S1) (hS2pos : 0 < volume S2) (η : ℝ) (hη : 0 < η)
    (hS1hs : ∀ t ∈ S1, η ≤ hs p t) (hS2hs : ∀ t ∈ S2, hs q t + η ≤ N.B q) (α β : ℝ)
    (hαβ : β < α) (hS1Φ : ∀ t ∈ S1, α < Φ' p t) (hS2Φ : ∀ t ∈ S2, Φ' q t ≤ β) : False := by
  classical
  set μ : Measure ℝ := volume.restrict (Icc N.t0 N.tf) with hμ
  have hμS : ∀ S, MeasurableSet S → S ⊆ Icc N.t0 N.tf → μ S = volume S := by
    intro S hS hSI
    rw [hμ, Measure.restrict_apply hS, inter_eq_left.2 hSI]
  have hfin : ∀ S, S ⊆ Icc N.t0 N.tf → volume S ≠ ⊤ := fun S hSI =>
    ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono hSI)
  set m1 := μ.real S1 with hm1
  set m2 := μ.real S2 with hm2
  have hm1pos : 0 < m1 := by
    rw [hm1, measureReal_def, hμS S1 hS1m hS1I]
    exact ENNReal.toReal_pos hS1pos.ne' (hfin S1 hS1I)
  have hm2pos : 0 < m2 := by
    rw [hm2, measureReal_def, hμS S2 hS2m hS2I]
    exact ENNReal.toReal_pos hS2pos.ne' (hfin S2 hS2I)
  set M0 := η * min m1 m2 with hM0
  have hM0pos : 0 < M0 := mul_pos hη (lt_min hm1pos hm2pos)
  set c1 := M0 / m1 with hc1
  set c2 := M0 / m2 with hc2
  have hc1m : c1 * m1 = M0 := div_mul_cancel₀ _ hm1pos.ne'
  have hc2m : c2 * m2 = M0 := div_mul_cancel₀ _ hm2pos.ne'
  have hc1η : c1 ≤ η := by
    rw [hc1, div_le_iff₀ hm1pos, hM0]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) hη.le
  have hc2η : c2 ≤ η := by
    rw [hc2, div_le_iff₀ hm2pos, hM0]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) hη.le
  have hc1pos : 0 < c1 := div_pos hM0pos hm1pos
  have hc2pos : 0 < c2 := div_pos hM0pos hm2pos
  let d1 : W → ℝ → ℝ := fun w t => if w = p then c1 * S1.indicator 1 t else 0
  let d2 : W → ℝ → ℝ := fun w t => if w = q then c2 * S2.indicator 1 t else 0
  let h : W → ℝ → ℝ := fun w t => hs w t - d1 w t + d2 w t
  have hd1m : ∀ w, Measurable (d1 w) := by
    intro w; by_cases hw : w = p
    · simp only [d1, hw, if_true]; exact (measurable_const.indicator hS1m).const_mul c1
    · simp only [d1, hw, if_false]; exact measurable_const
  have hd2m : ∀ w, Measurable (d2 w) := by
    intro w; by_cases hw : w = q
    · simp only [d2, hw, if_true]; exact (measurable_const.indicator hS2m).const_mul c2
    · simp only [d2, hw, if_false]; exact measurable_const
  have hdisj : p = q → ∀ t ∈ S1, t ∉ S2 := by
    intro hpq' t ht1 ht2
    have a1 := hS1Φ t ht1
    have a2 := hS2Φ t ht2
    rw [← hpq'] at a2
    linarith
  have hint1 : ∀ w, ∫ t, d1 w t ∂μ = if w = p then c1 * m1 else 0 := by
    intro w; by_cases hw : w = p
    · simp only [d1, hw, if_true]
      rw [integral_const_mul, integral_indicator_one hS1m]
    · simp [d1, hw]
  have hint2 : ∀ w, ∫ t, d2 w t ∂μ = if w = q then c2 * m2 else 0 := by
    intro w; by_cases hw : w = q
    · simp only [d2, hw, if_true]
      rw [integral_const_mul, integral_indicator_one hS2m]
    · simp [d2, hw]
  have hdint1 : ∀ w, Integrable (d1 w) μ := fun w =>
    Integrable.of_bound (hd1m w).aestronglyMeasurable c1 (Eventually.of_forall fun t => by
      by_cases hw : w = p <;> by_cases ht : t ∈ S1 <;>
        simp [d1, hw, ht, abs_of_pos hc1pos, hc1pos.le])
  have hdint2 : ∀ w, Integrable (d2 w) μ := fun w =>
    Integrable.of_bound (hd2m w).aestronglyMeasurable c2 (Eventually.of_forall fun t => by
      by_cases hw : w = q <;> by_cases ht : t ∈ S2 <;>
        simp [d2, hw, ht, abs_of_pos hc2pos, hc2pos.le])
  have hd1 : ∀ w t, 0 ≤ d1 w t ∧ d1 w t ≤ c1 ∧ (d1 w t ≠ 0 → w = p ∧ t ∈ S1) := by
    intro w t
    by_cases hw : w = p <;> by_cases ht : t ∈ S1 <;> simp [d1, hw, ht, hc1pos.le]
  have hd2 : ∀ w t, 0 ≤ d2 w t ∧ d2 w t ≤ c2 ∧ (d2 w t ≠ 0 → w = q ∧ t ∈ S2) := by
    intro w t
    by_cases hw : w = q <;> by_cases ht : t ∈ S2 <;> simp [d2, hw, ht, hc2pos.le]
  have hLam : Lam N h := by
    refine ⟨fun w => ((hhs.1 w).sub (hd1m w)).add (hd2m w), fun w => ?_, fun j => ?_⟩
    · filter_upwards [hhs.2.1 w] with t ht
      refine ⟨fun hti => ?_, fun hto => ?_⟩
      · obtain ⟨l, u⟩ := ht.1 hti
        obtain ⟨a0, a1, a2⟩ := hd1 w t
        obtain ⟨b0, b1, b2⟩ := hd2 w t
        show 0 ≤ hs w t - d1 w t + d2 w t ∧ hs w t - d1 w t + d2 w t ≤ N.B w
        constructor
        · by_cases hz : d1 w t = 0
          · rw [hz]; linarith
          · obtain ⟨rfl, ht1⟩ := a2 hz
            have := hS1hs t ht1
            linarith
        · by_cases hz : d2 w t = 0
          · rw [hz]; linarith
          · obtain ⟨rfl, ht2⟩ := b2 hz
            have := hS2hs t ht2
            by_cases hz1 : d1 w t = 0
            · rw [hz1]; linarith
            · obtain ⟨hwp, ht1⟩ := a2 hz1
              exact absurd ht2 (hdisj hwp.symm t ht1)
      · have h1 : t ∉ S1 := fun hh => hto (hS1I hh)
        have h2 : t ∉ S2 := fun hh => hto (hS2I hh)
        simp [h, d1, d2, h1, h2, ht.2 hto]
    · have hI : ∀ w, ∫ t in Icc N.t0 N.tf, h w t =
          (∫ t in Icc N.t0 N.tf, hs w t) - (if w = p then c1 * m1 else 0) +
            (if w = q then c2 * m2 else 0) := by
        intro w
        rw [← hint1 w, ← hint2 w]
        have I1 : ∫ t, (hs w t - d1 w t) ∂μ = ∫ t, hs w t ∂μ - ∫ t, d1 w t ∂μ :=
          integral_sub (lam_int N hhs w) (hdint1 w)
        have I2 : ∫ t, (hs w t - d1 w t + d2 w t) ∂μ =
            ∫ t, (hs w t - d1 w t) ∂μ + ∫ t, d2 w t ∂μ :=
          integral_add ((lam_int N hhs w).sub (hdint1 w)) (hdint2 w)
        show ∫ t, (hs w t - d1 w t + d2 w t) ∂μ = _
        rw [I2, I1]
      simp_rw [hI]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hhs.2.2 j]
      simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ,
        true_and]
      by_cases hj : N.com p = j
      · rw [if_pos hj, if_pos (hpq ▸ hj), hc1m, hc2m]; ring
      · rw [if_neg hj, if_neg (hpq ▸ hj)]; ring
  have hv := hvi h hLam
  have hΦint : ∀ w, Integrable (Φ' w) μ := fun w =>
    Integrable.of_bound (hΦ'm w).aestronglyMeasurable K (by
      filter_upwards [hK w] with t ht; rwa [Real.norm_eq_abs])
  have hterm : ∀ w, ∫ t in Icc N.t0 N.tf, Φ hs w t * (h w t - hs w t) =
      (if w = q then c2 * ∫ t in S2, Φ' q t ∂μ else 0) -
        (if w = p then c1 * ∫ t in S1, Φ' p t ∂μ else 0) := by
    intro w
    have e1 : ∫ t in Icc N.t0 N.tf, Φ hs w t * (h w t - hs w t) =
        ∫ t, (Φ' w t * d2 w t - Φ' w t * d1 w t) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hΦ'ae w] with t ht
      simp only [h]; rw [ht]; ring
    rw [e1, integral_sub ((hdint2 w).bdd_mul (hΦ'm w).aestronglyMeasurable
      (c := K) (by filter_upwards [hK w] with t ht; rwa [Real.norm_eq_abs]))
      ((hdint1 w).bdd_mul (hΦ'm w).aestronglyMeasurable
      (c := K) (by filter_upwards [hK w] with t ht; rwa [Real.norm_eq_abs]))]
    congr 1
    · by_cases hw : w = q
      · subst hw
        simp only [d2, if_true]
        rw [← integral_const_mul, ← integral_indicator hS2m]
        congr 1; funext t
        by_cases ht : t ∈ S2 <;> simp [ht, mul_comm]
      · simp [d2, hw]
    · by_cases hw : w = p
      · subst hw
        simp only [d1, if_true]
        rw [← integral_const_mul, ← integral_indicator hS1m]
        congr 1; funext t
        by_cases ht : t ∈ S1 <;> simp [ht, mul_comm]
      · simp [d1, hw]
  replace hv := hv.trans_eq (Finset.sum_congr rfl fun w _ => hterm w)
  rw [Finset.sum_sub_distrib] at hv
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hv
  have hb1 : α * m1 ≤ ∫ t in S1, Φ' p t ∂μ :=
    setIntegral_ge_of_const_le_real hS1m (by rw [hμS S1 hS1m hS1I]; exact hfin S1 hS1I)
      (fun t ht => (hS1Φ t ht).le) (hΦint p).integrableOn
  have hb2 : ∫ t in S2, Φ' q t ∂μ ≤ β * m2 := by
    have := setIntegral_ge_of_const_le_real (f := fun t => -Φ' q t) (c := -β) hS2m
      (by rw [hμS S2 hS2m hS2I]; exact hfin S2 hS2I)
      (fun t ht => neg_le_neg (hS2Φ t ht)) (hΦint q).neg.integrableOn
    rw [integral_neg] at this
    linarith
  have e1 : c1 * (α * m1) = α * M0 := by rw [← hc1m]; ring
  have e2 : c2 * (β * m2) = β * M0 := by rw [← hc2m]; ring
  have i1 := mul_le_mul_of_nonneg_left hb1 hc1pos.le
  have i2 := mul_le_mul_of_nonneg_left hb2 hc2pos.le
  nlinarith

end SideConstrainedDTA.Existence.Sol33

open SideConstrainedDTA.Existence SideConstrainedDTA.Existence.Sol33 in
theorem solution {I W E : Type*} [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W]
    (N : Model I W E) (hN : N.Basic) (Φ : (W → ℝ → ℝ) → W → ℝ → ℝ)
    (hΦ : ∀ h, Lam N h → ∀ p, AEStronglyMeasurable (Φ h p) (volume.restrict (Icc N.t0 N.tf)))
    (h1 : A1 N Φ) (hs : W → ℝ → ℝ) (hhs : Lam N hs) :
    IsDTCEq N Φ hs ↔
      ∀ h, Lam N h → 0 ≤ ∑ p, ∫ t in Icc N.t0 N.tf, Φ hs p t * (h p t - hs p t) := by
  classical
  set μ : Measure ℝ := volume.restrict (Icc N.t0 N.tf) with hμ
  choose Kp hKp using fun p => h1 hs hhs p
  set K : ℝ := ∑ p, |Kp p| with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun p _ => abs_nonneg _
  have hKb : ∀ p, ∀ t ∈ Icc N.t0 N.tf, |Φ hs p t| ≤ K := fun p t ht =>
    (hKp p t ht).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun q => |Kp q|)
      (fun q _ => abs_nonneg _) (Finset.mem_univ p)))
  have hKae : ∀ p, ∀ᵐ t ∂μ, |Φ hs p t| ≤ K := fun p => by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht using hKb p t ht
  constructor
  · rintro ⟨-, hν⟩ h hh
    choose ν hν using hν
    have hint : ∀ p, Integrable (fun t => Φ hs p t * (h p t - hs p t)) μ := fun p =>
      ((lam_int N hh p).sub (lam_int N hhs p)).bdd_mul (hΦ hs hhs p) (c := K)
        (by filter_upwards [hKae p] with t ht; rwa [Real.norm_eq_abs])
    have key : ∀ p, ν (N.com p) * (∫ t, h p t ∂μ - ∫ t, hs p t ∂μ) ≤
        ∫ t, Φ hs p t * (h p t - hs p t) ∂μ := by
      intro p
      rw [← integral_sub (lam_int N hh p) (lam_int N hhs p), ← integral_const_mul]
      refine integral_mono_ae (((lam_int N hh p).sub (lam_int N hhs p)).const_mul _)
        (hint p) ?_
      filter_upwards [hν (N.com p) p rfl, lam_bd N hh p, lam_bd N hhs p] with t ha hb hc
      rcases lt_trichotomy (h p t) (hs p t) with hlt | heq | hgt
      · have := ha.1 (by linarith [hb.1])
        show ν (N.com p) * (h p t - hs p t) ≤ Φ hs p t * (h p t - hs p t)
        nlinarith
      · simp [heq]
      · have := ha.2 (by linarith [hb.2])
        show ν (N.com p) * (h p t - hs p t) ≤ Φ hs p t * (h p t - hs p t)
        nlinarith
    have hzero : ∑ p, ν (N.com p) * (∫ t, h p t ∂μ - ∫ t, hs p t ∂μ) = 0 := by
      rw [← Finset.sum_fiberwise Finset.univ N.com]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hc : ∀ p ∈ Finset.univ.filter (fun p => N.com p = i),
          ν (N.com p) * (∫ t, h p t ∂μ - ∫ t, hs p t ∂μ) =
            ν i * (∫ t, h p t ∂μ - ∫ t, hs p t ∂μ) := fun p hp => by
        rw [(Finset.mem_filter.1 hp).2]
      rw [Finset.sum_congr rfl hc, ← Finset.mul_sum, Finset.sum_sub_distrib, hh.2.2 i,
        hhs.2.2 i, sub_self, mul_zero]
    calc (0:ℝ) = _ := hzero.symm
      _ ≤ _ := Finset.sum_le_sum fun p _ => key p
  · intro hvi
    refine ⟨hhs, fun i => ?_⟩
    set Φ' : W → ℝ → ℝ := fun p => (hΦ hs hhs p).mk _ with hΦ'
    have hΦ'm : ∀ p, Measurable (Φ' p) := fun p =>
      (hΦ hs hhs p).stronglyMeasurable_mk.measurable
    have hΦ'ae : ∀ p, Φ hs p =ᵐ[μ] Φ' p := fun p => (hΦ hs hhs p).ae_eq_mk
    have hK' : ∀ p, ∀ᵐ t ∂μ, |Φ' p t| ≤ K := fun p => by
      filter_upwards [hKae p, hΦ'ae p] with t h1 h2
      rwa [← h2]
    let U : Set ℝ := {α | -K ≤ α ∧ ∀ p, N.com p = i → ∀ᵐ t ∂μ, 0 < hs p t → Φ hs p t ≤ α}
    have hKU : K ∈ U := ⟨by linarith, fun p _ => by
      filter_upwards [hKae p] with t ht _
      exact (le_abs_self _).trans ht⟩
    have hbdd : BddBelow U := ⟨-K, fun a ha => ha.1⟩
    set ν := sInf U with hν
    have hνK : -K ≤ ν := le_csInf ⟨K, hKU⟩ fun a ha => ha.1
    refine ⟨ν, fun p hp => ?_⟩
    have P1 : ∀ᵐ t ∂μ, 0 < hs p t → Φ hs p t ≤ ν := by
      have hn : ∀ n : ℕ, ∀ᵐ t ∂μ, 0 < hs p t → Φ hs p t ≤ ν + 1 / ((n:ℝ) + 1) := by
        intro n
        have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
        obtain ⟨a, haU, hlt⟩ := exists_lt_of_csInf_lt ⟨K, hKU⟩
          (show sInf U < ν + 1 / ((n:ℝ) + 1) by linarith)
        filter_upwards [haU.2 p hp] with t ht hpos'
        exact (ht hpos').trans hlt.le
      filter_upwards [ae_all_iff.2 hn] with t ht hpos
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      exact lt_of_le_of_lt (ht n hpos) (by linarith)
    have P2 : ∀ᵐ t ∂μ, hs p t < N.B p → ν ≤ Φ hs p t := by
      by_contra hcon
      obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < μ {t | hs p t + 1 / ((n:ℝ) + 1) ≤ N.B p ∧
          Φ' p t ≤ ν - 1 / ((n:ℝ) + 1)} := by
        by_contra H
        push Not at H
        apply hcon
        have : ∀ n : ℕ, ∀ᵐ t ∂μ, ¬ (hs p t + 1 / ((n:ℝ) + 1) ≤ N.B p ∧
            Φ' p t ≤ ν - 1 / ((n:ℝ) + 1)) := fun n =>
          measure_eq_zero_iff_ae_notMem.1 (nonpos_iff_eq_zero.1 (H n))
        filter_upwards [ae_all_iff.2 this, hΦ'ae p] with t ht hte hlt
        rw [hte]
        by_contra hc
        push Not at hc
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt
          (show 0 < min (N.B p - hs p t) (ν - Φ' p t) from lt_min (by linarith) (by linarith))
        exact ht m ⟨by linarith [min_le_left (N.B p - hs p t) (ν - Φ' p t)],
          by linarith [min_le_right (N.B p - hs p t) (ν - Φ' p t)]⟩
      set ε : ℝ := 1 / ((n:ℝ) + 1) with hε
      have hε0 : 0 < ε := by positivity
      set T2 := {t | hs p t + ε ≤ N.B p ∧ Φ' p t ≤ ν - ε} with hT2
      have hT2m : MeasurableSet T2 :=
        (measurableSet_le ((hhs.1 p).add measurable_const) measurable_const).inter
          (measurableSet_le (hΦ'm p) measurable_const)
      have hβK : -K ≤ ν - ε := by
        by_contra hc
        push Not at hc
        have hsub : T2 ⊆ {t | ¬ |Φ' p t| ≤ K} := by
          intro t ht hle
          have := (abs_le.1 hle).1
          linarith [ht.2]
        have := measure_mono_null hsub (ae_iff.1 (hK' p))
        rw [this] at hn
        exact lt_irrefl _ hn
      have hαU : ν - ε / 2 ∉ U := by
        intro hU
        have := csInf_le hbdd hU
        linarith
      have : ¬ ∀ q, N.com q = i → ∀ᵐ t ∂μ, 0 < hs q t → Φ hs q t ≤ ν - ε / 2 :=
        fun h => hαU ⟨by linarith, h⟩
      obtain ⟨q, hqq⟩ := not_forall.1 this
      obtain ⟨hq, hqn⟩ := _root_.not_imp.1 hqq
      obtain ⟨m, hm⟩ : ∃ m : ℕ, 0 < μ {t | 1 / ((m:ℝ) + 1) ≤ hs q t ∧
          ν - ε / 2 < Φ' q t} := by
        by_contra H
        push Not at H
        apply hqn
        have : ∀ m : ℕ, ∀ᵐ t ∂μ, ¬ (1 / ((m:ℝ) + 1) ≤ hs q t ∧ ν - ε / 2 < Φ' q t) :=
          fun m => measure_eq_zero_iff_ae_notMem.1 (nonpos_iff_eq_zero.1 (H m))
        filter_upwards [ae_all_iff.2 this, hΦ'ae q] with t ht hte hpos
        rw [hte]
        by_contra hc
        push Not at hc
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
        exact ht k ⟨hk.le, hc⟩
      set S1 := Icc N.t0 N.tf ∩ {t | 1 / ((m:ℝ) + 1) ≤ hs q t ∧ ν - ε / 2 < Φ' q t}
      set S2 := Icc N.t0 N.tf ∩ T2
      have hS1m : MeasurableSet S1 := measurableSet_Icc.inter
        ((measurableSet_le measurable_const (hhs.1 q)).inter
          (measurableSet_lt measurable_const (hΦ'm q)))
      have hS2m : MeasurableSet S2 := measurableSet_Icc.inter hT2m
      have hvol : ∀ X : Set ℝ, MeasurableSet X → volume (Icc N.t0 N.tf ∩ X) = μ X := by
        intro X hX
        rw [hμ, Measure.restrict_apply hX, inter_comm]
      have hS1pos : 0 < volume S1 := by
        have := hvol {t | 1 / ((m:ℝ) + 1) ≤ hs q t ∧ ν - ε / 2 < Φ' q t}
          ((measurableSet_le measurable_const (hhs.1 q)).inter
          (measurableSet_lt measurable_const (hΦ'm q)))
        rw [← this] at hm
        exact hm
      have hS2pos : 0 < volume S2 := by
        have := hvol T2 hT2m
        rw [← this] at hn
        exact hn
      set η := min ε (1 / ((m:ℝ) + 1)) with hη
      have hη0 : 0 < η := lt_min hε0 (by positivity)
      exact transfer N Φ hs hhs Φ' hΦ'm hΦ'ae K hK' hvi q p (by rw [hq, hp]) S1 S2 hS1m hS2m
        inter_subset_left inter_subset_left hS1pos hS2pos η hη0
        (fun t ht => (min_le_right _ _).trans ht.2.1)
        (fun t ht => by have := ht.2.1; have := min_le_left ε (1 / ((m:ℝ) + 1)); linarith)
        (ν - ε / 2) (ν - ε) (by linarith) (fun t ht => ht.2.2) (fun t ht => ht.2.2)
    filter_upwards [P1, P2] with t a b
    exact ⟨a, b⟩
