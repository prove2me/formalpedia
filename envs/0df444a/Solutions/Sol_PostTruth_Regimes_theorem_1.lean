-- Prove2me | solution 1 for PostTruth.Regimes.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T06:46:29.146526+00:00
-- url     : https://prove2.me/submissions/d1ef2645-5865-4c1e-8214-4a88e7617cd1

import Mathlib
import Definitions.Def_PostTruth_Regimes_Model

set_option autoImplicit false

namespace PT71

open MeasureTheory PostTruth.Regimes
open scoped ENNReal

lemma law_zero (F : SplitLaw) {s : Set ℝ} (hs : MeasurableSet s)
    (h : ∀ r ∈ s, F.f r = 0) : F.law s = 0 := by
  unfold SplitLaw.law
  rw [withDensity_apply _ hs,
    setLIntegral_congr_fun hs (g := fun _ => (0 : ℝ≥0∞)) (fun r hr => by simp [h r hr])]
  simp

lemma law_compl (F : SplitLaw) : F.law (Set.Icc (0:ℝ) 1)ᶜ = 0 :=
  law_zero F measurableSet_Icc.compl (fun r hr => F.zero_off r hr)

lemma law_finite (F : SplitLaw) : IsFiniteMeasure F.law := by
  have hi : Integrable F.f := by
    by_contra h
    have := F.total
    rw [integral_undef h] at this
    norm_num at this
  exact isFiniteMeasure_withDensity_ofReal hi.2

lemma pos_density {g : ℝ → ℝ≥0∞} {μ : ℝ} (hμ : 0 < μ)
    (hg : ∀ x ∈ Set.Icc (0:ℝ) 1, ENNReal.ofReal μ < g x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    0 < volume.withDensity g (Set.Ioo a b) := by
  rw [withDensity_apply _ measurableSet_Ioo]
  have h1 : ∫⁻ _ in Set.Ioo a b, ENNReal.ofReal μ ≤ ∫⁻ x in Set.Ioo a b, g x :=
    setLIntegral_mono' measurableSet_Ioo
      (fun x hx => (hg x ⟨by linarith [hx.1], by linarith [hx.2]⟩).le)
  rw [setLIntegral_const, Real.volume_Ioo] at h1
  refine lt_of_lt_of_le ?_ h1
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hμ).ne' (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'

lemma F_pos (F : SplitLaw) (hF : F.FullSupportOn 0 1) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) : 0 < F.law (Set.Ioo a b) := by
  obtain ⟨⟨μ, hμ, hlt⟩, _⟩ := hF
  exact pos_density hμ
    (fun x hx => (ENNReal.ofReal_lt_ofReal_iff (lt_trans hμ (hlt x hx))).2 (hlt x hx)) ha hab hb

lemma H_pos {H : Measure ℝ} (hH : PriorFullSupportOn H 0 1) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) : 0 < H (Set.Ioo a b) := by
  obtain ⟨h, _, rfl, ⟨μ, hμ, hlt⟩, _⟩ := hH
  exact pos_density hμ hlt ha hab hb

lemma lt_parts {ν : Measure ℝ} [IsFiniteMeasure ν] {S T K I : Set ℝ}
    (hK : ν Kᶜ = 0) (hST : S ∩ K ⊆ T) (hIT : I ⊆ T) (hIS : Disjoint (S ∩ K) I)
    (hI : MeasurableSet I) (hpos : 0 < ν I) : ν S < ν T := by
  have h1 : ν S ≤ ν (S ∩ K) := by
    calc ν S ≤ ν (S ∩ K) + ν (S \ K) := measure_le_inter_add_sdiff ν S K
      _ = ν (S ∩ K) := by
        rw [measure_mono_null (show S \ K ⊆ Kᶜ from fun x hx => hx.2) hK, add_zero]
  calc ν S ≤ ν (S ∩ K) := h1
    _ < ν (S ∩ K) + ν I := ENNReal.lt_add_right (measure_ne_top _ _) hpos.ne'
    _ = ν (S ∩ K ∪ I) := (measure_union hIS hI).symm
    _ ≤ ν T := measure_mono (Set.union_subset hST hIT)

lemma ae_Ioo {H : Measure ℝ} (hH : PriorLaw H) : ∀ᵐ x ∂H, x ∈ Set.Ioo (0:ℝ) 1 := by
  haveI := hH.noAtoms
  rw [ae_iff]
  apply measure_mono_null (t := (Set.Icc (0:ℝ) 1)ᶜ ∪ ({0} ∪ {1}))
  · intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_Ioo, not_and_or, not_lt] at hx
    by_cases h : x ∈ Set.Icc (0:ℝ) 1
    · right
      rcases hx with hx | hx
      · left; exact le_antisymm hx h.1
      · right; exact le_antisymm h.2 hx
    · left; exact h
  · exact measure_union_null hH.conc
      (measure_union_null (measure_singleton 0) (measure_singleton 1))

/-! ## Part (i) -/

lemma qStar_pos {p : ℝ} (hp : 1/2 < p) : 0 < qStar p := by
  unfold qStar; exact div_pos (by linarith) (by linarith)

lemma qStar_lt_one {p : ℝ} (hp : 1/2 < p) : qStar p < 1 := by
  unfold qStar; rw [div_lt_one (by linarith)]; linarith

lemma gap_gt_one {p q : ℝ} (hp : 1/2 < p) (hq : 0 < q) (hqs : q < qStar p) :
    1 < gap p q := by
  unfold gap; unfold qStar at hqs
  rw [lt_div_iff₀ (by linarith)] at hqs
  rw [lt_div_iff₀ hq]; nlinarith

lemma probBayes_zero {p q : ℝ} {H : Measure ℝ} (hH : PriorLaw H) (F : SplitLaw)
    (hg : 1 < gap p q) (θ : State) : probBayes p q H F θ = 0 := by
  haveI := hH.noAtoms
  unfold probBayes
  apply measure_mono_null (t := {r | F.f r = 0})
  · intro r hr
    simp only [Set.mem_setOf_eq]
    by_contra hne
    have hr01 : r ∈ Set.Icc (0:ℝ) 1 := by
      by_contra h; exact hne (F.zero_off r h)
    have hm : MislearnsBayes p q H F θ r := hr
    unfold MislearnsBayes at hm
    cases θ with
    | L =>
      have h0 : F.f (r - gap p q) = 0 := F.zero_off _ (fun h => by linarith [h.1, hr01.2])
      have hemp : {x | Wrong State.L (piBayes p q F State.L r x)} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Wrong, piBayes, splitR, h0, mul_zero, zero_div,
          Set.mem_empty_iff_false, iff_false]
        norm_num
      rw [hemp, measure_empty] at hm
      exact lt_irrefl _ hm
    | R =>
      have h0 : F.f (r + gap p q) = 0 := F.zero_off _ (fun h => by linarith [h.2, hr01.1])
      have hsub : {x | Wrong State.R (piBayes p q F State.R r x)} ⊆ {0} := by
        intro x hx
        by_contra hx0
        have hx0' : x ≠ 0 := fun h => hx0 (by simp [h])
        simp only [Set.mem_setOf_eq, Wrong, piBayes, splitR, splitL, h0, mul_zero,
          add_zero] at hx
        rw [div_self (mul_ne_zero hx0' hne)] at hx
        norm_num at hx
      rw [measure_mono_null hsub (measure_singleton 0)] at hm
      exact lt_irrefl _ hm
  · exact law_zero F (F.meas (measurableSet_singleton 0)) (fun r hr => hr)

/-! ## DeGroot -/

lemma D1_pos {p x : ℝ} (hp : 1/2 < p) (hp1 : p ≤ 1) (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    0 < p * x + (1 - p) * (1 - x) := by
  have h1 := mul_pos (by linarith : (0:ℝ) < p) hx.1
  have h2 := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - p) (by linarith [hx.2] : (0:ℝ) ≤ 1 - x)
  linarith

lemma D2_pos {p x : ℝ} (hp : 1/2 < p) (hp1 : p ≤ 1) (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    0 < (1 - p) * x + p * (1 - x) := by
  have h1 := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - p) hx.1.le
  have h2 := mul_pos (by linarith : (0:ℝ) < p) (by linarith [hx.2] : (0:ℝ) < 1 - x)
  linarith

lemma postR_meas (p : ℝ) : Measurable (fun x => postR p x) := by
  unfold postR; fun_prop

lemma postL_meas (p : ℝ) : Measurable (fun x => postL p x) := by
  unfold postL; fun_prop

lemma postR_bounds {p x : ℝ} (hp : 1/2 < p) (hp1 : p ≤ 1) (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    0 ≤ postR p x ∧ postR p x ≤ 1 := by
  unfold postR
  have hD := D1_pos hp hp1 hx
  have h2 := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - p) (by linarith [hx.2] : (0:ℝ) ≤ 1 - x)
  refine ⟨div_nonneg (mul_nonneg (by linarith) hx.1.le) hD.le, ?_⟩
  rw [div_le_one hD]; linarith

lemma postL_bounds {p x : ℝ} (hp : 1/2 < p) (hp1 : p ≤ 1) (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    0 ≤ postL p x ∧ postL p x ≤ 1 := by
  unfold postL
  have hD := D2_pos hp hp1 hx
  have h2 := mul_nonneg (by linarith : (0:ℝ) ≤ p) (by linarith [hx.2] : (0:ℝ) ≤ 1 - x)
  refine ⟨div_nonneg (mul_nonneg (by linarith) hx.1.le) hD.le, ?_⟩
  rw [div_le_one hD]; linarith

lemma integrable_of_unit {H : Measure ℝ} (hH : PriorLaw H) {g : ℝ → ℝ} (hm : Measurable g)
    (hb : ∀ x ∈ Set.Ioo (0:ℝ) 1, 0 ≤ g x ∧ g x ≤ 1) : Integrable g H := by
  haveI := hH.isProb
  refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
  filter_upwards [ae_Ioo hH] with x hx
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [(hb x hx).1, (hb x hx).2]

lemma postL_flip {p x : ℝ} (hp : 1/2 < p) (hp1 : p ≤ 1) (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    postL p (1 - x) = 1 - postR p x := by
  unfold postL postR
  have hD := (D1_pos hp hp1 hx).ne'
  rw [show (1 - p) * (1 - x) + p * (1 - (1 - x)) = p * x + (1 - p) * (1 - x) by ring,
    eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hD]
  ring

lemma intL {p : ℝ} (hp : 1/2 < p) (hp1 : p ≤ 1) {H : Measure ℝ} (hH : PriorLaw H)
    (hsym : H.map (fun x : ℝ => 1 - x) = H) :
    ∫ x, postL p x ∂H = 1 - ∫ x, postR p x ∂H := by
  haveI := hH.isProb
  have iR := integrable_of_unit hH (postR_meas p) (fun x hx => postR_bounds hp hp1 hx)
  have e1 : ∫ x, postL p x ∂H = ∫ x, postL p x ∂(H.map (fun x : ℝ => 1 - x)) := by
    rw [hsym]
  rw [e1, integral_map (show Measurable (fun x : ℝ => 1 - x) by fun_prop).aemeasurable
    (postL_meas p).aestronglyMeasurable]
  rw [integral_congr_ae (g := fun x => 1 - postR p x) ?_]
  · rw [integral_sub (integrable_const 1) iR]
    simp
  · filter_upwards [ae_Ioo hH] with x hx
    exact postL_flip hp hp1 hx

lemma degroot_formula {p q : ℝ} (hp : 1/2 < p) (hp1 : p ≤ 1) {H : Measure ℝ}
    (hH : PriorLaw H) (hsym : H.map (fun x : ℝ => 1 - x) = H) (θ : State) (r : ℝ) :
    piDeGroot p q H θ r = shareR p q θ r * (∫ x, postR p x ∂H) +
      (1 - shareR p q θ r) * (1 - ∫ x, postR p x ∂H) := by
  have iR := integrable_of_unit hH (postR_meas p) (fun x hx => postR_bounds hp hp1 hx)
  have iL := integrable_of_unit hH (postL_meas p) (fun x hx => postL_bounds hp hp1 hx)
  unfold piDeGroot
  rw [integral_add (iR.const_mul _) (iL.const_mul _), integral_const_mul, integral_const_mul,
    intL hp hp1 hH hsym]

lemma postL_lt_postR {p x : ℝ} (hp : 1/2 < p) (hp1 : p ≤ 1) (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    postL p x < postR p x := by
  unfold postL postR
  have h1 := D1_pos hp hp1 hx
  have h2 := D2_pos hp hp1 hx
  rw [div_lt_div_iff₀ h2 h1]
  have key : p * x * ((1 - p) * x + p * (1 - x)) - (1 - p) * x * (p * x + (1 - p) * (1 - x))
      = x * (1 - x) * (2 * p - 1) := by ring
  have : 0 < x * (1 - x) * (2 * p - 1) :=
    mul_pos (mul_pos hx.1 (by linarith [hx.2])) (by linarith)
  linarith

lemma A_gt {p : ℝ} (hp : 1/2 < p) (hp1 : p ≤ 1) {H : Measure ℝ} (hH : PriorLaw H)
    (hsym : H.map (fun x : ℝ => 1 - x) = H) (hfs : PriorFullSupportOn H 0 1) :
    1/2 < ∫ x, postR p x ∂H := by
  have iR := integrable_of_unit hH (postR_meas p) (fun x hx => postR_bounds hp hp1 hx)
  have iL := integrable_of_unit hH (postL_meas p) (fun x hx => postL_bounds hp hp1 hx)
  have hpos : 0 < ∫ x, (postR p x - postL p x) ∂H := by
    rw [integral_pos_iff_support_of_nonneg_ae (f := fun x => postR p x - postL p x) ?_ (iR.sub iL)]
    · refine lt_of_lt_of_le (H_pos hfs le_rfl one_pos le_rfl) (measure_mono ?_)
      intro x hx
      exact (sub_pos.2 (postL_lt_postR hp hp1 hx)).ne'
    · filter_upwards [ae_Ioo hH] with x hx
      exact (sub_pos.2 (postL_lt_postR hp hp1 hx)).le
  rw [integral_sub iR iL, intL hp hp1 hH hsym] at hpos
  linarith

lemma wrongL_iff {A s : ℝ} (hA : 1/2 < A) :
    1/2 ≤ s * A + (1 - s) * (1 - A) ↔ 1/2 ≤ s := by
  have e : s * A + (1 - s) * (1 - A) - 1/2 = (2 * A - 1) * (s - 1/2) := by ring
  constructor
  · intro h
    by_contra hs
    push_neg at hs
    have : (2 * A - 1) * (s - 1/2) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  · intro h
    have : 0 ≤ (2 * A - 1) * (s - 1/2) := mul_nonneg (by linarith) (by linarith)
    linarith

lemma wrongR_iff {A s : ℝ} (hA : 1/2 < A) :
    s * A + (1 - s) * (1 - A) ≤ 1/2 ↔ s ≤ 1/2 := by
  have e : s * A + (1 - s) * (1 - A) - 1/2 = (2 * A - 1) * (s - 1/2) := by ring
  constructor
  · intro h
    by_contra hs
    push_neg at hs
    have : 0 < (2 * A - 1) * (s - 1/2) := mul_pos (by linarith) (by linarith)
    linarith
  · intro h
    have : (2 * A - 1) * (s - 1/2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith

lemma degroot_L_set {p q : ℝ} (hp : 1/2 < p) (hp1 : p ≤ 1) (hq : 0 < q) {H : Measure ℝ}
    (hH : PriorLaw H) (hsym : H.map (fun x : ℝ => 1 - x) = H)
    (hA : 1/2 < ∫ x, postR p x ∂H) :
    {r | MislearnsDeGroot p q H State.L r} = Set.Ici (rTilde p q) := by
  ext r
  simp only [Set.mem_setOf_eq, MislearnsDeGroot, Wrong, Set.mem_Ici]
  rw [degroot_formula hp hp1 hH hsym, wrongL_iff hA]
  simp only [shareR]
  have h2q : (0:ℝ) < 2 * q := by linarith
  constructor
  · intro h; unfold rTilde; rw [div_le_iff₀ h2q]; linarith
  · intro h; unfold rTilde at h; rw [div_le_iff₀ h2q] at h; linarith

lemma degroot_R_set {p q : ℝ} (hp : 1/2 < p) (hp1 : p ≤ 1) (hq : 0 < q) {H : Measure ℝ}
    (hH : PriorLaw H) (hsym : H.map (fun x : ℝ => 1 - x) = H)
    (hA : 1/2 < ∫ x, postR p x ∂H) :
    {r | MislearnsDeGroot p q H State.R r} = Set.Iic (rTildeR p q) := by
  ext r
  simp only [Set.mem_setOf_eq, MislearnsDeGroot, Wrong, Set.mem_Iic]
  rw [degroot_formula hp hp1 hH hsym, wrongR_iff hA]
  simp only [shareR]
  have h2q : (0:ℝ) < 2 * q := by linarith
  constructor
  · intro h; unfold rTildeR; rw [le_div_iff₀ h2q]; linarith
  · intro h; unfold rTildeR at h; rw [le_div_iff₀ h2q] at h; linarith

/-! ## Bayes -/

lemma half_le_ratio {x a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : b / (a + b) < x)
    (hx1 : x < 1) : 1/2 ≤ x * a / (x * a + (1 - x) * b) := by
  have hx0 : 0 < x := lt_of_le_of_lt (by positivity) hx
  rw [div_lt_iff₀ (by linarith)] at hx
  have h1 := mul_pos hx0 ha
  have h2 := mul_pos (sub_pos.2 hx1) hb
  rw [le_div_iff₀ (by linarith)]
  nlinarith

lemma ratio_le_half {x a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hx0 : 0 < x)
    (hx : x < b / (a + b)) : x * a / (x * a + (1 - x) * b) ≤ 1/2 := by
  have hc : b / (a + b) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hx1 : x < 1 := lt_trans hx hc
  rw [lt_div_iff₀ (by linarith)] at hx
  have h1 := mul_pos hx0 ha
  have h2 := mul_pos (sub_pos.2 hx1) hb
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma bayes_L_sub {p q : ℝ} (hg0 : 0 ≤ gap p q) {H : Measure ℝ}
    (hH : PriorFullSupportOn H 0 1) (F : SplitLaw) (hF : F.FullSupportOn 0 1) :
    Set.Icc (gap p q) 1 ⊆ {r | MislearnsBayes p q H F State.L r} := by
  intro r hr
  obtain ⟨⟨μ, hμ, hlt⟩, _⟩ := hF
  have ha : 0 < F.f (r - gap p q) :=
    lt_trans hμ (hlt _ ⟨by linarith [hr.1], by linarith [hr.2]⟩)
  have hb : 0 < F.f r := lt_trans hμ (hlt _ ⟨by linarith [hr.1], hr.2⟩)
  have hc0 : 0 ≤ F.f r / (F.f (r - gap p q) + F.f r) := by positivity
  have hc1 : F.f r / (F.f (r - gap p q) + F.f r) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  show 0 < H _
  refine lt_of_lt_of_le (H_pos hH hc0 hc1 le_rfl) (measure_mono ?_)
  intro x hx
  simp only [Set.mem_setOf_eq, Wrong, piBayes, splitR, splitL]
  exact half_le_ratio ha hb hx.1 hx.2

lemma bayes_R_sub {p q : ℝ} (hg0 : 0 ≤ gap p q) {H : Measure ℝ}
    (hH : PriorFullSupportOn H 0 1) (F : SplitLaw) (hF : F.FullSupportOn 0 1) :
    Set.Icc 0 (1 - gap p q) ⊆ {r | MislearnsBayes p q H F State.R r} := by
  intro r hr
  obtain ⟨⟨μ, hμ, hlt⟩, _⟩ := hF
  have ha : 0 < F.f r := lt_trans hμ (hlt _ ⟨hr.1, by linarith [hr.2]⟩)
  have hb : 0 < F.f (r + gap p q) :=
    lt_trans hμ (hlt _ ⟨by linarith [hr.1], by linarith [hr.2]⟩)
  have hc0 : 0 < F.f (r + gap p q) / (F.f r + F.f (r + gap p q)) := by positivity
  have hc1 : F.f (r + gap p q) / (F.f r + F.f (r + gap p q)) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  show 0 < H _
  refine lt_of_lt_of_le (H_pos hH le_rfl hc0 hc1) (measure_mono ?_)
  intro x hx
  simp only [Set.mem_setOf_eq, Wrong, piBayes, splitR, splitL]
  exact ratio_le_half ha hb hx.1 hx.2

/-! ## Part (ii) -/

lemma rTildeR_eq {p q : ℝ} (hq : 0 < q) : rTildeR p q = 1 - rTilde p q := by
  unfold rTildeR rTilde
  have := hq.ne'
  field_simp
  ring

lemma part2 {p q : ℝ} (hp1 : 1/2 < p) (hp2 : p ≤ 1) (hqs : qStar p < q) (hq2 : q < 1/2)
    {H : Measure ℝ} (hH : PriorLaw H) (hsym : H.map (fun x : ℝ => 1 - x) = H)
    (hHf : PriorFullSupportOn H 0 1) (F : SplitLaw) (hFf : F.FullSupportOn 0 1)
    (θ : State) : probDeGroot p q H F θ < probBayes p q H F θ := by
  have hq : 0 < q := lt_trans (qStar_pos hp1) hqs
  have hqs' := hqs
  unfold qStar at hqs'
  rw [div_lt_iff₀ (by linarith)] at hqs'
  have hg0 : 0 < gap p q := by
    unfold gap; exact div_pos (mul_pos (by linarith) (by linarith)) hq
  have hg1 : gap p q < 1 := by
    unfold gap; rw [div_lt_iff₀ hq]; nlinarith
  have hgr : gap p q < rTilde p q := by
    unfold gap rTilde
    have h : 2 * (2 * p - 1) * (1 - q) < 1 - 2 * (1 - q) * (1 - p) := by nlinarith
    rw [div_lt_div_iff₀ hq (by linarith)]
    nlinarith [mul_lt_mul_of_pos_left h hq]
  have hA := A_gt hp1 hp2 hH hsym hHf
  haveI := law_finite F
  unfold probDeGroot probBayes
  cases θ with
  | L =>
    rw [degroot_L_set hp1 hp2 hq hH hsym hA]
    apply lt_parts (K := Set.Icc 0 1) (I := Set.Ioo (gap p q) (min 1 (rTilde p q)))
      (law_compl F)
    · rintro r ⟨hr1, hr2⟩
      exact bayes_L_sub hg0.le hHf F hFf ⟨by rw [Set.mem_Ici] at hr1; linarith, hr2.2⟩
    · intro r hr
      exact bayes_L_sub hg0.le hHf F hFf ⟨hr.1.le, hr.2.le.trans (min_le_left _ _)⟩
    · rw [Set.disjoint_left]
      rintro r ⟨hr1, _⟩ hr2
      rw [Set.mem_Ici] at hr1
      linarith [hr2.2, min_le_right 1 (rTilde p q)]
    · exact measurableSet_Ioo
    · exact F_pos F hFf hg0.le (lt_min hg1 hgr) (min_le_left _ _)
  | R =>
    have hrr : rTildeR p q < 1 - gap p q := by rw [rTildeR_eq hq]; linarith
    rw [degroot_R_set hp1 hp2 hq hH hsym hA]
    apply lt_parts (K := Set.Icc 0 1) (I := Set.Ioo (max 0 (rTildeR p q)) (1 - gap p q))
      (law_compl F)
    · rintro r ⟨hr1, hr2⟩
      exact bayes_R_sub hg0.le hHf F hFf ⟨hr2.1, by rw [Set.mem_Iic] at hr1; linarith⟩
    · intro r hr
      exact bayes_R_sub hg0.le hHf F hFf ⟨(le_max_left _ _).trans hr.1.le, hr.2.le⟩
    · rw [Set.disjoint_left]
      rintro r ⟨hr1, _⟩ hr2
      rw [Set.mem_Iic] at hr1
      linarith [hr2.1, le_max_right 0 (rTildeR p q)]
    · exact measurableSet_Ioo
    · exact F_pos F hFf (le_max_left _ _) (max_lt (by linarith) hrr) (by linarith)

end PT71

open MeasureTheory PostTruth.Regimes in
theorem solution (p : ℝ) (hp : (1 / 2 : ℝ) < p ∧ p ≤ 1) :
    0 < qStar p ∧ qStar p < 1 ∧
    ∀ (H : Measure ℝ), PriorLaw H → Symmetric H → ∀ (F : SplitLaw),
      (∀ q : ℝ, 0 < q → q < qStar p → ∀ θ : State,
        probBayes p q H F θ ≤ probDeGroot p q H F θ) ∧
      (∀ q : ℝ, qStar p < q → q < 1 / 2 →
        PriorFullSupportOn H 0 1 → F.FullSupportOn 0 1 →
        ∀ θ : State,
          probDeGroot p q H F θ < probBayes p q H F θ) := by
  obtain ⟨hp1, hp2⟩ := hp
  refine ⟨PT71.qStar_pos hp1, PT71.qStar_lt_one hp1, fun H hH hsym F => ⟨?_, ?_⟩⟩
  · intro q hq hqs θ
    rw [PT71.probBayes_zero hH F (PT71.gap_gt_one hp1 hq hqs) θ]
    exact zero_le
  · intro q hqs hq2 hHf hFf θ
    exact PT71.part2 hp1 hp2 hqs hq2 hH hsym hHf F hFf θ
