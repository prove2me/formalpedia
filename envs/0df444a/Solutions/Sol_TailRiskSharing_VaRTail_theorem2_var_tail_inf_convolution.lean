-- Prove2me | solution 1 for TailRiskSharing.VaRTail.theorem2_var_tail_inf_convolution
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T04:44:51.470977+00:00
-- url     : https://prove2.me/submissions/cb027b48-4fbf-4570-b6cc-ebe973dab150

import Mathlib
import Definitions.Def_TailRiskSharing_VaRTail_Setting
import Theorems.Thm_TailRiskSharing_VaRTail_exists_quantile_uniform

open MeasureTheory Filter Topology

namespace VaRTailAux
open TailRiskSharing.VaRConv TailRiskSharing.VaRTail

structure IsCDF (F : ℝ → ℝ) : Prop where
  mono : Monotone F
  rc : ∀ x, ContinuousWithinAt F (Set.Ici x) x
  bot : Tendsto F atBot (𝓝 0)
  top : Tendsto F atTop (𝓝 1)
  nonneg : ∀ x, 0 ≤ F x
  le_one : ∀ x, F x ≤ 1

section CDF
variable {F : ℝ → ℝ}

lemma bdd_ge (hF : IsCDF F) {t : ℝ} (ht : 0 < t) : BddBelow {x | t ≤ F x} := by
  obtain ⟨x0, hx0⟩ := (hF.bot.eventually (gt_mem_nhds ht)).exists
  refine ⟨x0, fun y hy => ?_⟩
  by_contra h
  push Not at h
  exact absurd (lt_of_le_of_lt (hF.mono h.le) hx0) (not_lt.2 hy)

lemma bdd_gt (hF : IsCDF F) {t : ℝ} (ht : 0 < t) : BddBelow {x | t < F x} :=
  (bdd_ge hF ht).mono fun x hx => le_of_lt (show t < F x from hx)

lemma ne_gt (hF : IsCDF F) {t : ℝ} (ht : t < 1) : ({x | t < F x} : Set ℝ).Nonempty :=
  (hF.top.eventually (lt_mem_nhds ht)).exists

lemma ne_ge (hF : IsCDF F) {t : ℝ} (ht : t < 1) : ({x | t ≤ F x} : Set ℝ).Nonempty := by
  obtain ⟨x, hx⟩ := ne_gt hF ht
  exact ⟨x, le_of_lt (show t < F x from hx)⟩

lemma le_F_sInf (hF : IsCDF F) {t : ℝ} (h1 : t < 1) : t ≤ F (sInf {x | t ≤ F x}) := by
  set q := sInf {x | t ≤ F x}
  have hne := ne_ge hF h1
  have hy : ∀ y ∈ Set.Ioi q, t ≤ F y := fun y hy => by
    obtain ⟨s, hs, hsy⟩ := exists_lt_of_csInf_lt hne hy
    exact le_trans hs (hF.mono hsy.le)
  have hc : Tendsto F (𝓝[>] q) (𝓝 (F q)) :=
    (hF.rc q).mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  exact ge_of_tendsto hc (eventually_nhdsWithin_of_forall hy)

lemma galois (hF : IsCDF F) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (x : ℝ) :
    sInf {y | t ≤ F y} ≤ x ↔ t ≤ F x := by
  constructor
  · intro h; exact le_trans (le_F_sInf hF h1) (hF.mono h)
  · intro h; exact csInf_le (bdd_ge hF h0) h

lemma F_le_of_lt_sInf (hF : IsCDF F) {t : ℝ} (h0 : 0 < t) {x : ℝ}
    (hx : x < sInf {y | t < F y}) : F x ≤ t := by
  by_contra h
  push Not at h
  exact absurd (csInf_le (bdd_gt hF h0) h) (not_le.2 hx)

lemma lt_F_of_sInf_lt (hF : IsCDF F) {t : ℝ} (h1 : t < 1) {x : ℝ}
    (hx : sInf {y | t < F y} < x) : t < F x := by
  obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt (ne_gt hF h1) hx
  exact lt_of_lt_of_le hs (hF.mono hsx.le)

lemma sInf_gt_le_sInf_ge (hF : IsCDF F) {t s : ℝ} (h0 : 0 < t) (hts : t < s) (hs1 : s < 1) :
    sInf {y | t < F y} ≤ sInf {y | s ≤ F y} :=
  csInf_le_csInf (bdd_gt hF h0) (ne_ge hF hs1) fun _ hy => lt_of_lt_of_le hts hy

end CDF

variable {Ω : Type*} [MeasurableSpace Ω]

lemma distFn_eq_cdf (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X)
    (x : ℝ) : distFn P X x = ProbabilityTheory.cdf (P.map X) x := by
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  rw [ProbabilityTheory.cdf_eq_real, map_measureReal_apply hX measurableSet_Iic]
  rfl

lemma isCDF_distFn (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X) :
    IsCDF (distFn P X) := by
  have h : distFn P X = ProbabilityTheory.cdf (P.map X) := funext (distFn_eq_cdf P hX)
  rw [h]
  exact ⟨ProbabilityTheory.monotone_cdf _, fun x => (ProbabilityTheory.cdf (P.map X)).right_continuous x,
    ProbabilityTheory.tendsto_cdf_atBot _, ProbabilityTheory.tendsto_cdf_atTop _,
    ProbabilityTheory.cdf_nonneg _, ProbabilityTheory.cdf_le_one _⟩

section U
variable {P : Measure Ω} [IsProbabilityMeasure P] {X U : Ω → ℝ}

lemma U_preimage (hU : IsQuantileUniform P X U) {s : Set ℝ} (hs : MeasurableSet s) :
    P.real (U ⁻¹' s) = volume.real (s ∩ Set.Icc 0 1) := by
  rw [← map_measureReal_apply hU.1 hs, hU.2.1, measureReal_restrict_apply hs]

lemma U_le (hU : IsQuantileUniform P X U) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    P.real {ω | U ω ≤ t} = t := by
  have := U_preimage hU (measurableSet_Iic (a := t))
  have he : Set.Iic t ∩ Set.Icc (0:ℝ) 1 = Set.Icc 0 t := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]; constructor
    · rintro ⟨a, b, _⟩; exact ⟨b, a⟩
    · rintro ⟨a, b⟩; exact ⟨b, a, le_trans b h1⟩
  rw [he, Real.volume_real_Icc_of_le h0, sub_zero] at this
  exact this

lemma U_Ioc (hU : IsQuantileUniform P X U) {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (h1 : b ≤ 1) :
    P.real {ω | a < U ω ∧ U ω ≤ b} = b - a := by
  have := U_preimage hU (measurableSet_Ioc (a := a) (b := b))
  have he : Set.Ioc a b ∩ Set.Icc (0:ℝ) 1 = Set.Ioc a b := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc]; constructor
    · rintro ⟨h, _⟩; exact h
    · rintro ⟨p, q⟩; exact ⟨⟨p, q⟩, by linarith, by linarith⟩
  rw [he, Real.volume_real_Ioc_of_le hab] at this
  exact this

lemma U_ae_Ioo (hU : IsQuantileUniform P X U) : ∀ᵐ ω ∂P, 0 < U ω ∧ U ω < 1 := by
  have h : ∀ᵐ y ∂(P.map U), 0 < y ∧ y < 1 := by
    rw [hU.2.1, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [Measure.ae_ne volume (0:ℝ), Measure.ae_ne volume (1:ℝ)] with y h0 h1 hy
    exact ⟨lt_of_le_of_ne hy.1 (Ne.symm h0), lt_of_le_of_ne hy.2 h1⟩
  exact ae_of_ae_map hU.1.aemeasurable h

lemma key_ae (hX : Measurable X) (hU : IsQuantileUniform P X U) :
    ∀ᵐ ω ∂P, ∀ x, (X ω ≤ x ↔ U ω ≤ distFn P X x) := by
  filter_upwards [U_ae_Ioo hU, hU.2.2] with ω h1 h2 x
  rw [← h2]
  unfold VaRL
  simp only [sub_sub_cancel]
  exact galois (isCDF_distFn P hX) h1.1 h1.2 x

lemma cut_meas (hX : Measurable X) (hU : IsQuantileUniform P X U) (ε α : ℝ) :
    Measurable (cutAt P ε α X U) :=
  Measurable.ite (measurableSet_le hU.1 measurable_const) hX measurable_const

omit [IsProbabilityMeasure P] in
lemma cut_le {ε α : ℝ} {ω : Ω} (hu : U ω ≤ 1 - α) : cutAt P ε α X U ω = X ω := by
  unfold cutAt; rw [if_pos hu]

omit [IsProbabilityMeasure P] in
lemma cut_gt {ε α : ℝ} {ω : Ω} (hu : ¬ U ω ≤ 1 - α) : cutAt P ε α X U ω = VaRR P (α + ε) X := by
  unfold cutAt; rw [if_neg hu]

/-- Display (17). -/
theorem distFn_cut (ε : ℝ) (hε0 : 0 < ε) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 - ε)
    (hX : Measurable X) (hU : IsQuantileUniform P X U) (x : ℝ) :
    distFn P (cutAt P ε α X U) x =
      if x < VaRR P (α + ε) X then distFn P X x
      else if x < VaRL P α X then distFn P X x + α
      else 1 := by
  have hF := isCDF_distFn P hX
  set F := distFn P X with hFdef
  set c := VaRR P (α + ε) X with hc
  have hcd : c = sInf {y | 1 - (α + ε) < F y} := rfl
  have hqd : VaRL P α X = sInf {y | 1 - α ≤ F y} := rfl
  have hkey := key_ae hX hU
  split_ifs with h1 h2
  · -- x < c
    have hFx : F x ≤ 1 - (α + ε) := F_le_of_lt_sInf hF (by linarith) (hcd ▸ h1)
    have he : ({ω | cutAt P ε α X U ω ≤ x} : Set Ω) =ᵐ[P] ({ω | U ω ≤ F x} : Set Ω) := by
      filter_upwards [hkey] with ω hω
      apply propext
      show (cutAt P ε α X U ω ≤ x) ↔ (U ω ≤ F x)
      by_cases hu : U ω ≤ 1 - α
      · rw [cut_le hu]; exact hω x
      · rw [cut_gt hu]; constructor
        · intro h; exact absurd h (not_le.2 h1)
        · intro h; exact absurd (le_trans h (by linarith)) hu
    unfold distFn
    rw [measureReal_congr he, U_le hU (hF.nonneg x) (hF.le_one x)]
  · -- c ≤ x < q
    have hFx : F x < 1 - α := by
      by_contra h; push Not at h
      exact absurd ((galois hF (by linarith) (by linarith) x).2 h) (not_le.2 (hqd ▸ h2))
    have he : ({ω | cutAt P ε α X U ω ≤ x} : Set Ω)ᶜ =ᵐ[P] ({ω | F x < U ω ∧ U ω ≤ 1 - α} : Set Ω) := by
      filter_upwards [hkey] with ω hω
      apply propext
      show ¬ (cutAt P ε α X U ω ≤ x) ↔ (F x < U ω ∧ U ω ≤ 1 - α)
      by_cases hu : U ω ≤ 1 - α
      · rw [cut_le hu, hω x]; constructor
        · intro h; exact ⟨lt_of_not_ge h, hu⟩
        · intro h; exact not_le.2 h.1
      · rw [cut_gt hu]; constructor
        · intro h; exact absurd (not_lt.1 h1) h
        · intro h; exact absurd h.2 hu
    have hm : MeasurableSet ({ω | cutAt P ε α X U ω ≤ x} : Set Ω) :=
      measurableSet_le (cut_meas hX hU ε α) measurable_const
    have := probReal_compl_eq_one_sub (μ := P) hm
    rw [measureReal_congr (s := ({ω | cutAt P ε α X U ω ≤ x} : Set Ω)ᶜ) he, U_Ioc hU (hF.nonneg x) hFx.le (by linarith)] at this
    unfold distFn
    linarith
  · -- x ≥ q
    have hFx : 1 - α ≤ F x := (galois hF (by linarith) (by linarith) x).1 (hqd ▸ not_lt.1 h2)
    have he : ({ω | cutAt P ε α X U ω ≤ x} : Set Ω)ᶜ =ᵐ[P] (∅ : Set Ω) := by
      filter_upwards [hkey] with ω hω
      apply propext
      show ¬ (cutAt P ε α X U ω ≤ x) ↔ False
      rw [iff_false, not_not]
      by_cases hu : U ω ≤ 1 - α
      · rw [cut_le hu, hω x]; linarith
      · rw [cut_gt hu]; exact not_lt.1 h1
    have hm : MeasurableSet ({ω | cutAt P ε α X U ω ≤ x} : Set Ω) :=
      measurableSet_le (cut_meas hX hU ε α) measurable_const
    have := probReal_compl_eq_one_sub (μ := P) hm
    rw [measureReal_congr (s := ({ω | cutAt P ε α X U ω ≤ x} : Set Ω)ᶜ) he, measureReal_empty] at this
    unfold distFn
    linarith

/-- Display (18). -/
theorem varR_cut (ε : ℝ) (hε0 : 0 < ε) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 - ε)
    (hX : Measurable X) (hU : IsQuantileUniform P X U) :
    VaRR P ε (cutAt P ε α X U) = VaRR P (α + ε) X := by
  have hF := isCDF_distFn P hX
  have hcd : VaRR P (α + ε) X = sInf {y | 1 - (α + ε) < distFn P X y} := rfl
  have hmem : ∀ y, VaRR P (α + ε) X < y → 1 - ε < distFn P (cutAt P ε α X U) y := by
    intro y hy
    rw [distFn_cut ε hε0 α hα0 hα1 hX hU y, if_neg (not_lt.2 hy.le)]
    split_ifs with h
    · have := lt_F_of_sInf_lt hF (t := 1 - (α + ε)) (by linarith) (hcd ▸ hy)
      linarith
    · linarith
  have hnot : ∀ y, y < VaRR P (α + ε) X → distFn P (cutAt P ε α X U) y ≤ 1 - ε := by
    intro y hy
    rw [distFn_cut ε hε0 α hα0 hα1 hX hU y, if_pos hy]
    have := F_le_of_lt_sInf hF (t := 1 - (α + ε)) (by linarith) (hcd ▸ hy)
    linarith
  unfold VaRR
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨_, hmem _ (lt_add_one (VaRR P (α + ε) X))⟩
  · intro a ha
    by_contra h
    push Not at h
    exact absurd (hnot a h) (not_le.2 ha)
  · intro w hw
    refine ⟨(VaRR P (α + ε) X + w) / 2, hmem _ (by linarith), by linarith⟩

omit [IsProbabilityMeasure P] in
lemma measurable_of_L0 {Y : Ω → ℝ} (hY : Y ∈ (L0 : Set (Ω → ℝ))) : Measurable Y := hY

/-- Proof of (i): `F_{X-Y}(x) ≤ F_{X^[α]}(x)` for `x ≥ VaR^R_{α+ε}(X)`. -/
theorem distFn_le_cut (ε : ℝ) (hε0 : 0 < ε) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 - ε)
    (hX : Measurable X) (hU : IsQuantileUniform P X U)
    {Y : Ω → ℝ} (hY : Measurable Y) (hYvar : VaRL P α Y = 0)
    (x : ℝ) (hx : VaRR P (α + ε) X ≤ x) :
    distFn P (X - Y) x ≤ distFn P (cutAt P ε α X U) x := by
  have hFY := isCDF_distFn P hY
  have hY0 : 1 - α ≤ distFn P Y 0 :=
    (galois hFY (t := 1 - α) (by linarith) (by linarith) 0).1 (le_of_eq hYvar)
  have hsub : {ω | (X - Y) ω ≤ x} ⊆ {ω | X ω ≤ x} ∪ {ω | Y ω ≤ 0}ᶜ := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Pi.sub_apply] at hω
    by_cases h : Y ω ≤ 0
    · left; show X ω ≤ x; linarith
    · right; exact h
  have h1 : distFn P (X - Y) x ≤ distFn P X x + (1 - distFn P Y 0) := by
    unfold distFn
    calc P.real {ω | (X - Y) ω ≤ x} ≤ P.real ({ω | X ω ≤ x} ∪ {ω | Y ω ≤ 0}ᶜ) :=
          measureReal_mono hsub
      _ ≤ P.real {ω | X ω ≤ x} + P.real {ω | Y ω ≤ 0}ᶜ := measureReal_union_le _ _
      _ = _ := by rw [probReal_compl_eq_one_sub (measurableSet_le hY measurable_const)]
  have h2 : distFn P (X - Y) x ≤ 1 := by unfold distFn; exact measureReal_le_one
  rw [distFn_cut ε hε0 α hα0 hα1 hX hU x, if_neg (not_lt.2 hx)]
  split_ifs
  · linarith
  · exact h2

lemma max_shift {a b t s : ℝ} (hts : t ≤ s) (h : max (a - t) 0 = max (b - t) 0) :
    max (a - s) 0 = max (b - s) 0 := by
  simp only [max_def] at *
  split_ifs at * <;> linarith

lemma tail_cut_formula (ε : ℝ) (hε0 : 0 < ε) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1 - ε)
    (hX : Measurable X) (hU : IsQuantileUniform P X U) (x : ℝ) :
    max (distFn P (cutAt P ε β X U) x - (1 - ε)) 0 =
      min (max (distFn P X x - (1 - (β + ε))) 0) ε := by
  have hF := isCDF_distFn P hX
  have hcd : VaRR P (β + ε) X = sInf {y | 1 - (β + ε) < distFn P X y} := rfl
  have hqd : VaRL P β X = sInf {y | 1 - β ≤ distFn P X y} := rfl
  rw [distFn_cut ε hε0 β hβ0 hβ1 hX hU x]
  split_ifs with h1 h2
  · have := F_le_of_lt_sInf hF (t := 1 - (β + ε)) (by linarith) (hcd ▸ h1)
    simp only [max_def, min_def]; split_ifs <;> linarith
  · have : distFn P X x < 1 - β := by
      by_contra h; push Not at h
      exact absurd ((galois hF (by linarith) (by linarith) x).2 h) (not_le.2 (hqd ▸ h2))
    simp only [max_def, min_def]; split_ifs <;> linarith
  · have : 1 - β ≤ distFn P X x :=
      (galois hF (by linarith) (by linarith) x).1 (hqd ▸ not_lt.1 h2)
    simp only [max_def, min_def]; split_ifs <;> linarith

/-- Proof of (iv): tail equivalence passes to the cut variables. -/
theorem tail_cut {Z V : Ω → ℝ} (ε : ℝ) (hε0 : 0 < ε) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 - ε)
    (hX : Measurable X) (hZ : Measurable Z)
    (hU : IsQuantileUniform P X U) (hV : IsQuantileUniform P Z V)
    (hXZ : TailEquiv P (α + ε) X Z) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδα : δ < α) :
    TailEquiv P ε (cutAt P ε (α - δ) X U) (cutAt P ε (α - δ) Z V) := by
  intro x
  rw [tail_cut_formula ε hε0 (α - δ) (by linarith) (by linarith) hX hU x,
    tail_cut_formula ε hε0 (α - δ) (by linarith) (by linarith) hZ hV x,
    max_shift (by linarith) (hXZ x)]

end U

end VaRTailAux

namespace VaRTailAux
open TailRiskSharing.VaRConv TailRiskSharing.VaRTail

variable {Ω : Type*} [MeasurableSpace Ω]

section Main
variable {P : Measure Ω} [IsProbabilityMeasure P] {X U : Ω → ℝ}

lemma le_F_sInf_gt {F : ℝ → ℝ} (hF : IsCDF F) {t : ℝ} (h1 : t < 1) :
    t ≤ F (sInf {x | t < F x}) := by
  have hy : ∀ y ∈ Set.Ioi (sInf {x | t < F x}), t ≤ F y := fun y hy => (lt_F_of_sInf_lt hF h1 hy).le
  have hc : Tendsto F (𝓝[>] (sInf {x | t < F x})) (𝓝 (F (sInf {x | t < F x}))) :=
    (hF.rc _).mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  exact ge_of_tendsto hc (eventually_nhdsWithin_of_forall hy)

omit [IsProbabilityMeasure P] in
lemma U_ae_ne (hU : IsQuantileUniform P X U) (b : ℝ) : ∀ᵐ ω ∂P, U ω ≠ b := by
  have h : ∀ᵐ y ∂(P.map U), y ≠ b := by
    rw [hU.2.1]; exact ae_restrict_of_ae (Measure.ae_ne volume b)
  exact ae_of_ae_map hU.1.aemeasurable h

lemma distFn_sub_le {Y : Ω → ℝ} (hY : Measurable Y) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hYvar : VaRL P α Y = 0) (x : ℝ) :
    distFn P (X - Y) x ≤ distFn P X x + α := by
  have hFY := isCDF_distFn P hY
  have hY0 : 1 - α ≤ distFn P Y 0 :=
    (galois hFY (t := 1 - α) (by linarith) (by linarith) 0).1 (le_of_eq hYvar)
  have hsub : {ω | (X - Y) ω ≤ x} ⊆ {ω | X ω ≤ x} ∪ {ω | Y ω ≤ 0}ᶜ := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Pi.sub_apply] at hω
    by_cases h : Y ω ≤ 0
    · left; show X ω ≤ x; linarith
    · right; exact h
  have h1 : distFn P (X - Y) x ≤ distFn P X x + (1 - distFn P Y 0) := by
    unfold distFn
    calc P.real {ω | (X - Y) ω ≤ x} ≤ P.real ({ω | X ω ≤ x} ∪ {ω | Y ω ≤ 0}ᶜ) :=
          measureReal_mono hsub
      _ ≤ P.real {ω | X ω ≤ x} + P.real {ω | Y ω ≤ 0}ᶜ := measureReal_union_le _ _
      _ = _ := by rw [probReal_compl_eq_one_sub (measurableSet_le hY measurable_const)]
  linarith

omit [IsProbabilityMeasure P] in
lemma distFn_sub_const {Y : Ω → ℝ} (m x : ℝ) :
    distFn P (fun ω => Y ω - m) x = distFn P Y (x + m) := by
  unfold distFn
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor <;> intro h <;> linarith

lemma eq_of_forall_le_iff' {a b : ℝ} (h : ∀ x, a ≤ x ↔ b ≤ x) : a = b :=
  le_antisymm ((h b).2 le_rfl) ((h a).1 le_rfl)

lemma VaRL_sub_const {Y : Ω → ℝ} (hY : Measurable Y) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (m : ℝ) : VaRL P α (fun ω => Y ω - m) = VaRL P α Y - m := by
  have hY' : Measurable (fun ω => Y ω - m) := hY.sub_const m
  apply eq_of_forall_le_iff'
  intro x
  rw [show VaRL P α (fun ω => Y ω - m) = sInf {y | 1 - α ≤ distFn P (fun ω => Y ω - m) y} from rfl,
    galois (isCDF_distFn P hY') (by linarith) (by linarith), distFn_sub_const,
    show VaRL P α Y = sInf {y | 1 - α ≤ distFn P Y y} from rfl,
    ← galois (isCDF_distFn P hY) (by linarith) (by linarith) (x + m)]
  exact sub_le_iff_le_add.symm

lemma VaRL_sub_cut (ε : ℝ) (hε0 : 0 < ε) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 - ε)
    (hX : Measurable X) (hU : IsQuantileUniform P X U) :
    VaRL P α (X - cutAt P ε α X U) = 0 := by
  have hF := isCDF_distFn P hX
  have hDm : Measurable (X - cutAt P ε α X U) := hX.sub (cut_meas hX hU ε α)
  have hFD := isCDF_distFn P hDm
  have hcd : VaRR P (α + ε) X = sInf {y | 1 - (α + ε) < distFn P X y} := rfl
  have hpos : ∀ᵐ ω ∂P, 0 ≤ (X - cutAt P ε α X U) ω := by
    filter_upwards [key_ae hX hU] with ω hω
    show 0 ≤ X ω - cutAt P ε α X U ω
    by_cases hu : U ω ≤ 1 - α
    · rw [cut_le hu]; simp
    · rw [cut_gt hu]
      by_contra h
      push Not at h
      have h1 : X ω < VaRR P (α + ε) X := by linarith
      have h2 := F_le_of_lt_sInf hF (t := 1 - (α + ε)) (by linarith) (hcd ▸ h1)
      have h3 := (hω (X ω)).1 le_rfl
      exact hu (by linarith)
  have h0 : 1 - α ≤ distFn P (X - cutAt P ε α X U) 0 := by
    have hs : {ω | U ω ≤ 1 - α} ⊆ {ω | (X - cutAt P ε α X U) ω ≤ 0} := by
      intro ω hu
      show X ω - cutAt P ε α X U ω ≤ 0
      rw [cut_le hu]; simp
    have := measureReal_mono (μ := P) hs
    rw [U_le hU (by linarith) (by linarith)] at this
    exact this
  have hneg : ∀ y < 0, distFn P (X - cutAt P ε α X U) y = 0 := by
    intro y hy
    have he : ({ω | (X - cutAt P ε α X U) ω ≤ y} : Set Ω) =ᵐ[P] (∅ : Set Ω) := by
      filter_upwards [hpos] with ω hω
      apply propext
      show (X - cutAt P ε α X U) ω ≤ y ↔ False
      constructor
      · intro h; linarith
      · intro h; exact h.elim
    unfold distFn
    rw [measureReal_congr he, measureReal_empty]
  show sInf {y | 1 - α ≤ distFn P (X - cutAt P ε α X U) y} = 0
  apply le_antisymm
  · exact csInf_le (bdd_ge hFD (by linarith)) h0
  · apply le_csInf ⟨0, h0⟩
    intro y hy
    by_contra h
    push Not at h
    have := hneg y h
    have hy' : 1 - α ≤ distFn P (X - cutAt P ε α X U) y := hy
    linarith

omit [IsProbabilityMeasure P] in
lemma alloc_two_iff (X : Ω → ℝ) (Xs : Fin 2 → Ω → ℝ) :
    Xs ∈ Allocations (L0 : Set (Ω → ℝ)) 2 X ↔
      Measurable (Xs 0) ∧ Measurable (Xs 1) ∧ ∀ ω, Xs 0 ω + Xs 1 ω = X ω := by
  simp only [Allocations, Set.mem_setOf_eq, Fin.forall_fin_two, Fin.sum_univ_two]
  constructor
  · rintro ⟨⟨h0, h1⟩, h⟩; exact ⟨h0, h1, h⟩
  · rintro ⟨h0, h1, h⟩; exact ⟨⟨h0, h1⟩, h⟩

omit [MeasurableSpace Ω] in
lemma sum_two (f g : (Ω → ℝ) → ℝ) (Xs : Fin 2 → Ω → ℝ) :
    (∑ i, (![f, g] : Fin 2 → (Ω → ℝ) → ℝ) i (Xs i)) = f (Xs 0) + g (Xs 1) := by
  simp [Fin.sum_univ_two]

omit [IsProbabilityMeasure P] in
lemma infConv_le (f g : (Ω → ℝ) → ℝ) {X Y Z : Ω → ℝ} (hY : Measurable Y) (hZ : Measurable Z)
    (h : ∀ ω, Y ω + Z ω = X ω) :
    infConv (L0 : Set (Ω → ℝ)) ![f, g] X ≤ ((f Y + g Z : ℝ) : EReal) := by
  have hm : (![Y, Z] : Fin 2 → Ω → ℝ) ∈ Allocations (L0 : Set (Ω → ℝ)) 2 X :=
    (alloc_two_iff X _).2 ⟨hY, hZ, h⟩
  unfold infConv
  refine (iInf₂_le _ hm).trans (le_of_eq ?_)
  rw [sum_two]
  rfl

omit [IsProbabilityMeasure P] in
lemma le_infConv (f g : (Ω → ℝ) → ℝ) {X : Ω → ℝ} {e : EReal}
    (h : ∀ Y Z : Ω → ℝ, Measurable Y → Measurable Z → (∀ ω, Y ω + Z ω = X ω) →
      e ≤ ((f Y + g Z : ℝ) : EReal)) :
    e ≤ infConv (L0 : Set (Ω → ℝ)) ![f, g] X := by
  unfold infConv
  refine le_iInf₂ fun Xs hXs => ?_
  obtain ⟨h0, h1, hs⟩ := (alloc_two_iff X Xs).1 hXs
  rw [sum_two]
  exact h _ _ h0 h1 hs

omit [IsProbabilityMeasure P] in
lemma exists_of_infConv_lt (f g : (Ω → ℝ) → ℝ) {X : Ω → ℝ} {e : EReal}
    (h : infConv (L0 : Set (Ω → ℝ)) ![f, g] X < e) :
    ∃ Y Z : Ω → ℝ, Measurable Y ∧ Measurable Z ∧ (∀ ω, Y ω + Z ω = X ω) ∧
      ((f Y + g Z : ℝ) : EReal) < e := by
  by_contra hc
  push Not at hc
  exact absurd h (not_lt.2 (le_infConv f g fun Y Z hY hZ hs => hc Y Z hY hZ hs))

/-- Tail dominance: the key step of the proof of Theorem 2 (i). -/
theorem rho_cut_le (ε : ℝ) (hε0 : 0 < ε) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 - ε)
    (hX : Measurable X) (hU : IsQuantileUniform P X U) (ρ : (Ω → ℝ) → ℝ)
    (hρm : IsMonotone P L0 ρ) (hρt : IsTailRiskMeasure P L0 ε ρ) {Z : Ω → ℝ}
    (hZ : Measurable Z)
    (hdom : ∀ x, max (distFn P Z x - (1 - ε)) 0 ≤
      max (distFn P (cutAt P ε α X U) x - (1 - ε)) 0) :
    ρ (cutAt P ε α X U) ≤ ρ Z := by
  have hF := isCDF_distFn P hX
  have hFZ := isCDF_distFn P hZ
  have hcd : VaRR P (α + ε) X = sInf {y | 1 - (α + ε) < distFn P X y} := rfl
  have hqd : VaRL P α X = sInf {y | 1 - α ≤ distFn P X y} := rfl
  have hWm : Measurable (cutAt P ε α X U) := cut_meas hX hU ε α
  obtain ⟨Zt, hZt⟩ : ∃ Zt : Ω → ℝ, ∀ ω, Zt ω = if (1 - α - ε < U ω ∧ U ω < 1 - α) then
      sInf {y | U ω + α ≤ distFn P Z y} else cutAt P ε α X U ω := ⟨_, fun ω => rfl⟩
  have hQgal : ∀ ω, (1 - α - ε < U ω ∧ U ω < 1 - α) → ∀ x,
      (sInf {y | U ω + α ≤ distFn P Z y} ≤ x ↔ U ω + α ≤ distFn P Z x) := by
    intro ω hR x
    exact galois hFZ (by linarith [hR.1]) (by linarith [hR.2]) x
  have hRm : MeasurableSet {ω | 1 - α - ε < U ω ∧ U ω < 1 - α} :=
    (measurableSet_lt measurable_const hU.1).inter (measurableSet_lt hU.1 measurable_const)
  have hZtm : Measurable Zt := by
    apply measurable_of_Iic
    intro x
    have he : Zt ⁻¹' Set.Iic x =
        ({ω | 1 - α - ε < U ω ∧ U ω < 1 - α} ∩ {ω | U ω + α ≤ distFn P Z x}) ∪
        ({ω | 1 - α - ε < U ω ∧ U ω < 1 - α}ᶜ ∩ {ω | cutAt P ε α X U ω ≤ x}) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff,
        Set.mem_setOf_eq, Set.mem_compl_iff]
      by_cases hR : (1 - α - ε < U ω ∧ U ω < 1 - α)
      · rw [hZt ω, if_pos hR, hQgal ω hR x]; tauto
      · rw [hZt ω, if_neg hR]; tauto
    rw [he]
    exact (hRm.inter (measurableSet_le (hU.1.add_const α) measurable_const)).union
      (hRm.compl.inter (measurableSet_le hWm measurable_const))
  -- monotonicity: X^[α] ≤ Zt a.s.
  have hle : ∀ᵐ ω ∂P, cutAt P ε α X U ω ≤ Zt ω := by
    filter_upwards [key_ae hX hU] with ω hω
    by_cases hR : (1 - α - ε < U ω ∧ U ω < 1 - α)
    · rw [hZt ω, if_pos hR, cut_le (le_of_lt hR.2)]
      have hy1 : U ω + α ≤ distFn P Z (sInf {y | U ω + α ≤ distFn P Z y}) :=
        le_F_sInf hFZ (by linarith [hR.2])
      have hy2 := hdom (sInf {y | U ω + α ≤ distFn P Z y})
      have hG : U ω + α ≤ distFn P (cutAt P ε α X U) (sInf {y | U ω + α ≤ distFn P Z y}) := by
        by_contra hc
        push Not at hc
        have h3 : distFn P Z (sInf {y | U ω + α ≤ distFn P Z y}) - (1 - ε) ≤
            max (distFn P (cutAt P ε α X U) (sInf {y | U ω + α ≤ distFn P Z y}) - (1 - ε)) 0 :=
          le_trans (le_max_left _ _) hy2
        rcases max_cases (distFn P (cutAt P ε α X U) (sInf {y | U ω + α ≤ distFn P Z y}) - (1 - ε)) 0
          with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at h3 <;> linarith [hR.1]
      rw [distFn_cut ε hε0 α hα0 hα1 hX hU] at hG
      rw [hω]
      split_ifs at hG with h1 h2
      · have := F_le_of_lt_sInf hF (t := 1 - (α + ε)) (by linarith) (hcd ▸ h1)
        linarith [hR.1]
      · linarith
      · have := (galois hF (by linarith) (by linarith) _).1 (hqd ▸ not_lt.1 h2)
        linarith [hR.2]
    · rw [hZt ω, if_neg hR]
  -- tail equivalence of Zt and Z
  have htail : TailEquiv P ε Zt Z := by
    intro x
    by_cases hx : x < VaRR P (α + ε) X
    · have hFx := F_le_of_lt_sInf hF (t := 1 - (α + ε)) (by linarith) (hcd ▸ hx)
      have hGx : distFn P (cutAt P ε α X U) x = distFn P X x := by
        rw [distFn_cut ε hε0 α hα0 hα1 hX hU, if_pos hx]
      have hFZx : distFn P Z x ≤ 1 - ε := by
        have h := hdom x
        rw [hGx, max_eq_right (show distFn P X x - (1 - ε) ≤ 0 by linarith)] at h
        have := le_max_left (distFn P Z x - (1 - ε)) 0
        linarith
      have hsub : ({ω | Zt ω ≤ x} : Set Ω) ≤ᵐ[P] ({ω | U ω ≤ 1 - α - ε} : Set Ω) := by
        filter_upwards [key_ae hX hU] with ω hω
        intro h
        change Zt ω ≤ x at h
        show U ω ≤ 1 - α - ε
        by_cases hR : (1 - α - ε < U ω ∧ U ω < 1 - α)
        · rw [hZt ω, if_pos hR, hQgal ω hR x] at h
          linarith
        · rw [hZt ω, if_neg hR] at h
          by_cases hu : U ω ≤ 1 - α
          · rw [cut_le hu, hω x] at h
            linarith
          · rw [cut_gt hu] at h
            exact absurd h (not_le.2 hx)
      have hZtx : distFn P Zt x ≤ 1 - α - ε := by
        unfold distFn
        rw [← U_le hU (t := 1 - α - ε) (by linarith) (by linarith)]
        exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    · push Not at hx
      have hFc : 1 - (α + ε) ≤ distFn P X x :=
        le_trans (le_F_sInf_gt hF (by linarith)) (hF.mono (hcd ▸ hx))
      have hlo : max (1 - α - ε) (distFn P Z x - α) ≤ 1 - α :=
        max_le (by linarith) (by linarith [hFZ.le_one x])
      have he : ({ω | Zt ω ≤ x} : Set Ω)ᶜ =ᵐ[P]
          ({ω | max (1 - α - ε) (distFn P Z x - α) < U ω ∧ U ω ≤ 1 - α} : Set Ω) := by
        filter_upwards [key_ae hX hU, U_ae_ne hU (1 - α)] with ω hω hb
        apply propext
        show ¬ (Zt ω ≤ x) ↔ (max (1 - α - ε) (distFn P Z x - α) < U ω ∧ U ω ≤ 1 - α)
        rw [max_lt_iff]
        by_cases hR : (1 - α - ε < U ω ∧ U ω < 1 - α)
        · rw [hZt ω, if_pos hR, hQgal ω hR x]
          constructor
          · intro h
            push Not at h
            exact ⟨⟨hR.1, by linarith⟩, hR.2.le⟩
          · intro h
            push Not
            linarith [h.1.2]
        · rw [hZt ω, if_neg hR]
          by_cases hu : U ω ≤ 1 - α
          · have hUa : U ω ≤ 1 - α - ε := by
              by_contra h
              push Not at h
              exact hR ⟨h, lt_of_le_of_ne hu hb⟩
            rw [cut_le hu, hω x]
            constructor
            · intro h; exact absurd (by linarith) h
            · intro h; linarith [h.1.1]
          · rw [cut_gt hu]
            constructor
            · intro h; exact absurd hx h
            · intro h; exact absurd h.2 hu
      have hm : MeasurableSet ({ω | Zt ω ≤ x} : Set Ω) := measurableSet_le hZtm measurable_const
      have h1 := probReal_compl_eq_one_sub (μ := P) hm
      rw [measureReal_congr (s := ({ω | Zt ω ≤ x} : Set Ω)ᶜ) he,
        U_Ioc hU (le_trans (by linarith) (le_max_left _ _)) hlo (by linarith)] at h1
      have hval : distFn P Zt x = α + max (1 - α - ε) (distFn P Z x - α) := by
        have h2 : distFn P Zt x = P.real ({ω | Zt ω ≤ x} : Set Ω) := rfl
        rw [h2]; linarith
      rw [hval]
      have := hFZ.le_one x
      simp only [max_def]
      split_ifs <;> linarith
  calc ρ (cutAt P ε α X U) ≤ ρ Zt := hρm _ hWm _ hZtm hle
    _ = ρ Z := hρt _ hZtm _ hZ htail

/-- Theorem 2 (i). -/
theorem infConv_VaRL_eq (ε : ℝ) (hε0 : 0 < ε) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 - ε)
    (hX : Measurable X) (hU : IsQuantileUniform P X U) (ρ : (Ω → ℝ) → ℝ)
    (hρm : IsMonetary P L0 ρ) (hρt : IsTailRiskMeasure P L0 ε ρ) :
    infConv (L0 : Set (Ω → ℝ)) ![VaRL P α, ρ] X = ((ρ (cutAt P ε α X U) : ℝ) : EReal) := by
  apply le_antisymm
  · have h := infConv_le (VaRL P α) ρ (X := X) (hX.sub (cut_meas hX hU ε α))
      (cut_meas hX hU ε α) (fun ω => by simp)
    rwa [VaRL_sub_cut ε hε0 α hα0 hα1 hX hU, zero_add] at h
  · apply le_infConv
    intro Y Z hY hZ hs
    have hY' : Measurable (fun ω => Y ω - VaRL P α Y) := hY.sub_const _
    have hZ' : Measurable (fun ω => Z ω + VaRL P α Y) := hZ.add_const _
    have hv : VaRL P α (fun ω => Y ω - VaRL P α Y) = 0 := by
      rw [VaRL_sub_const hY hα0 (by linarith)]; ring
    have htr : ρ Z = ρ (fun ω => Z ω + VaRL P α Y) - VaRL P α Y := by
      have := hρm.2 (fun ω => Z ω + VaRL P α Y) hZ' (VaRL P α Y)
      simp only [add_sub_cancel_right] at this
      exact this
    have hXY : X - (fun ω => Y ω - VaRL P α Y) = fun ω => Z ω + VaRL P α Y := by
      funext ω; simp only [Pi.sub_apply]; linarith [hs ω]
    have hdom : ∀ x, max (distFn P (fun ω => Z ω + VaRL P α Y) x - (1 - ε)) 0 ≤
        max (distFn P (cutAt P ε α X U) x - (1 - ε)) 0 := by
      intro x
      rw [← hXY]
      by_cases hx : VaRR P (α + ε) X ≤ x
      · exact max_le_max (by linarith [distFn_le_cut ε hε0 α hα0 hα1 hX hU hY' hv x hx]) le_rfl
      · push Not at hx
        have h1 := distFn_sub_le (X := X) hY' hα0 (by linarith) hv x
        have h2 := F_le_of_lt_sInf (isCDF_distFn P hX) (t := 1 - (α + ε)) (by linarith) hx
        rw [max_eq_right (by linarith)]
        exact le_max_right _ _
    have := rho_cut_le ε hε0 α hα0 hα1 hX hU ρ hρm.1 hρt hZ' hdom
    rw [htr]
    exact EReal.coe_le_coe_iff.2 (by linarith)

/-- Theorem 2 (ii). -/
theorem optimal_alloc (ε : ℝ) (hε0 : 0 < ε) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 - ε)
    (hX : Measurable X) (hU : IsQuantileUniform P X U) (ρ : (Ω → ℝ) → ℝ)
    (hρm : IsMonetary P L0 ρ) (hρt : IsTailRiskMeasure P L0 ε ρ) :
    IsOptimalAllocation (L0 : Set (Ω → ℝ)) ![VaRL P α, ρ] X
      ![X - cutAt P ε α X U, cutAt P ε α X U] := by
  refine ⟨(alloc_two_iff X _).2 ⟨hX.sub (cut_meas hX hU ε α), cut_meas hX hU ε α, ?_⟩, ?_⟩
  · intro ω; simp
  · rw [sum_two, infConv_VaRL_eq ε hε0 α hα0 hα1 hX hU ρ hρm hρt]
    simp [VaRL_sub_cut ε hε0 α hα0 hα1 hX hU]

lemma VaRR_le_VaRL {Y : Ω → ℝ} (hY : Measurable Y) {α δ : ℝ} (hα1 : α < 1) (hδ0 : 0 < δ)
    (hδα : δ < α) : VaRR P α Y ≤ VaRL P (α - δ) Y :=
  csInf_le_csInf (bdd_gt (isCDF_distFn P hY) (by linarith)) (ne_ge (isCDF_distFn P hY) (by linarith))
    (fun y hy => by
      have h : 1 - (α - δ) ≤ distFn P Y y := hy
      show 1 - α < distFn P Y y
      linarith)

lemma VaRL_anti {Y : Ω → ℝ} (hY : Measurable Y) {α δ δ0 : ℝ} (hα1 : α < 1) (hδ0 : 0 ≤ δ)
    (hδδ : δ ≤ δ0) (hδα : δ0 < α) : VaRL P (α - δ) Y ≤ VaRL P (α - δ0) Y :=
  csInf_le_csInf (bdd_ge (isCDF_distFn P hY) (by linarith)) (ne_ge (isCDF_distFn P hY) (by linarith))
    (fun y hy => by
      have h : 1 - (α - δ0) ≤ distFn P Y y := hy
      show 1 - (α - δ) ≤ distFn P Y y
      linarith)

/-- Theorem 2 (iii). -/
theorem tendsto_VaRR (ε : ℝ) (hε0 : 0 < ε) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 - ε)
    (hX : Measurable X) (hU : IsQuantileUniform P X U) (ρ : (Ω → ℝ) → ℝ)
    (hρm : IsMonetary P L0 ρ) (hρt : IsTailRiskMeasure P L0 ε ρ) :
    Tendsto (fun δ : ℝ => ((ρ (cutAt P ε (α - δ) X U) : ℝ) : EReal)) (𝓝[>] 0)
      (𝓝 (infConv (L0 : Set (Ω → ℝ)) ![VaRR P α, ρ] X)) := by
  have hrep : ∀ δ, 0 < δ → δ < α → ((ρ (cutAt P ε (α - δ) X U) : ℝ) : EReal) =
      infConv (L0 : Set (Ω → ℝ)) ![VaRL P (α - δ), ρ] X :=
    fun δ h0 h1 => (infConv_VaRL_eq ε hε0 (α - δ) (by linarith) (by linarith) hX hU ρ hρm hρt).symm
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [Ioo_mem_nhdsGT hα0] with δ hδ
    rw [hrep δ hδ.1 hδ.2]
    refine lt_of_lt_of_le ha (le_infConv _ _ fun Y Z hY hZ hs => ?_)
    exact (infConv_le _ _ hY hZ hs).trans
      (EReal.coe_le_coe_iff.2 (by linarith [VaRR_le_VaRL (P := P) hY (α := α) (by linarith) hδ.1 hδ.2]))
  · intro a ha
    obtain ⟨Y, Z, hY, hZ, hs, hlt⟩ := exists_of_infConv_lt _ _ ha
    obtain ⟨r', hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have hr1' : VaRR P α Y + ρ Z < r' := EReal.coe_lt_coe_iff.1 hr1
    obtain ⟨η, hη⟩ : ∃ η, η = r' - (VaRR P α Y + ρ Z) := ⟨_, rfl⟩
    have hηp : 0 < η := by rw [hη]; linarith
    have hFY := isCDF_distFn P hY
    have hF1 : 1 - α < distFn P Y (VaRR P α Y + η / 2) :=
      lt_F_of_sInf_lt hFY (by linarith) (by show VaRR P α Y < VaRR P α Y + η / 2; linarith)
    obtain ⟨δ0, hδ0⟩ : ∃ δ0, δ0 = min (distFn P Y (VaRR P α Y + η / 2) - (1 - α)) (α / 2) :=
      ⟨_, rfl⟩
    have hδ0p : 0 < δ0 := by rw [hδ0]; exact lt_min (by linarith) (by linarith)
    have hδ0a : δ0 < α := by
      rw [hδ0]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hδ0le : δ0 ≤ distFn P Y (VaRR P α Y + η / 2) - (1 - α) := by
      rw [hδ0]; exact min_le_left _ _
    have hV : VaRL P (α - δ0) Y ≤ VaRR P α Y + η / 2 :=
      csInf_le (bdd_ge hFY (by linarith))
        (show 1 - (α - δ0) ≤ distFn P Y (VaRR P α Y + η / 2) by linarith)
    filter_upwards [Ioo_mem_nhdsGT hδ0p] with δ hδ
    rw [hrep δ hδ.1 (by linarith [hδ.2])]
    have hanti := VaRL_anti (P := P) hY (α := α) (by linarith) hδ.1.le hδ.2.le hδ0a
    refine lt_of_le_of_lt (infConv_le _ _ hY hZ hs) (lt_trans ?_ hr2)
    exact EReal.coe_lt_coe_iff.2 (by linarith)

/-- The inf-convolution of a functional with a monetary risk measure is monetary. -/
theorem infConv_monetary (f : (Ω → ℝ) → ℝ) (ρ : (Ω → ℝ) → ℝ) (hρm : IsMonetary P L0 ρ) :
    IsMonetaryE P L0 (fun X => infConv (L0 : Set (Ω → ℝ)) ![f, ρ] X) := by
  constructor
  · intro X hX Y hY hXY
    apply le_infConv
    intro Y1 Y2 h1 h2 hs
    have hX' : Measurable X := hX
    have hY' : Measurable Y := hY
    have hm : Measurable (fun ω => Y2 ω - (Y ω - X ω)) := h2.sub (hY'.sub hX')
    refine (infConv_le f ρ (X := X) h1 hm (fun ω => by
      have := hs ω
      show Y1 ω + (Y2 ω - (Y ω - X ω)) = X ω
      linarith)).trans (EReal.coe_le_coe_iff.2 ?_)
    have : ρ (fun ω => Y2 ω - (Y ω - X ω)) ≤ ρ Y2 :=
      hρm.1 _ hm _ h2 (by filter_upwards [hXY] with ω hω; linarith)
    linarith
  · intro X hX m
    show infConv (L0 : Set (Ω → ℝ)) ![f, ρ] (fun ω => X ω - m) =
      infConv (L0 : Set (Ω → ℝ)) ![f, ρ] X - (m : EReal)
    apply le_antisymm
    · rw [EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot m)) (Or.inl (EReal.coe_ne_top m))]
      apply le_infConv
      intro Y1 Y2 h1 h2 hs
      have hm : Measurable (fun ω => Y2 ω - m) := h2.sub_const m
      have := infConv_le f ρ (X := fun ω => X ω - m) h1 hm (fun ω => by
        have := hs ω
        show Y1 ω + (Y2 ω - m) = X ω - m
        linarith)
      have htr := hρm.2 Y2 h2 m
      rw [htr] at this
      calc infConv (L0 : Set (Ω → ℝ)) ![f, ρ] (fun ω => X ω - m) + m
          ≤ ((f Y1 + (ρ Y2 - m) : ℝ) : EReal) + m := add_le_add_left this _
        _ = ((f Y1 + ρ Y2 : ℝ) : EReal) := by rw [← EReal.coe_add]; congr 1; ring
    · apply le_infConv
      intro Y1 Y2 h1 h2 hs
      rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot m)) (Or.inl (EReal.coe_ne_top m))]
      have hm : Measurable (fun ω => Y2 ω + m) := h2.add_const m
      have := infConv_le f ρ (X := X) h1 hm (fun ω => by
        have := hs ω
        change Y1 ω + Y2 ω = X ω - m at this
        show Y1 ω + (Y2 ω + m) = X ω
        linarith)
      have htr := hρm.2 (fun ω => Y2 ω + m) hm m
      simp only [add_sub_cancel_right] at htr
      calc infConv (L0 : Set (Ω → ℝ)) ![f, ρ] X ≤ ((f Y1 + ρ (fun ω => Y2 ω + m) : ℝ) : EReal) := this
        _ = ((f Y1 + ρ Y2 : ℝ) : EReal) + m := by rw [← EReal.coe_add]; congr 1; linarith

end Main

end VaRTailAux

open TailRiskSharing.VaRConv TailRiskSharing.VaRTail

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (ρ : (Ω → ℝ) → ℝ) (hρm : IsMonetary P TailRiskSharing.VaRConv.L0 ρ) (hρt : IsTailRiskMeasure P TailRiskSharing.VaRConv.L0 ε ρ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 - ε) :
    -- (i)
    (∀ X ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ)), ∀ U : Ω → ℝ, IsQuantileUniform P X U →
      TailRiskSharing.VaRConv.infConv TailRiskSharing.VaRConv.L0 ![TailRiskSharing.VaRConv.VaRL P α, ρ] X = ((ρ (cutAt P ε α X U) : ℝ) : EReal)) ∧
    -- (ii)
    (∀ X ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ)), ∀ U : Ω → ℝ, IsQuantileUniform P X U →
      TailRiskSharing.VaRConv.IsOptimalAllocation TailRiskSharing.VaRConv.L0 ![TailRiskSharing.VaRConv.VaRL P α, ρ] X ![X - cutAt P ε α X U, cutAt P ε α X U]) ∧
    -- (iii)
    (∀ X ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ)), ∀ U : Ω → ℝ, IsQuantileUniform P X U →
      Tendsto (fun δ : ℝ => ((ρ (cutAt P ε (α - δ) X U) : ℝ) : EReal)) (𝓝[>] 0)
        (𝓝 (TailRiskSharing.VaRConv.infConv TailRiskSharing.VaRConv.L0 ![TailRiskSharing.VaRConv.VaRR P α, ρ] X))) ∧
    -- (iv)
    (IsMonetaryE P TailRiskSharing.VaRConv.L0 (fun X => TailRiskSharing.VaRConv.infConv TailRiskSharing.VaRConv.L0 ![TailRiskSharing.VaRConv.VaRR P α, ρ] X) ∧
      IsTailRiskMeasureE P TailRiskSharing.VaRConv.L0 (α + ε) (fun X => TailRiskSharing.VaRConv.infConv TailRiskSharing.VaRConv.L0 ![TailRiskSharing.VaRConv.VaRR P α, ρ] X) ∧
      IsMonetaryE P TailRiskSharing.VaRConv.L0 (fun X => TailRiskSharing.VaRConv.infConv TailRiskSharing.VaRConv.L0 ![TailRiskSharing.VaRConv.VaRL P α, ρ] X) ∧
      IsTailRiskMeasureE P TailRiskSharing.VaRConv.L0 (α + ε) (fun X => TailRiskSharing.VaRConv.infConv TailRiskSharing.VaRConv.L0 ![TailRiskSharing.VaRConv.VaRL P α, ρ] X)) := by
  refine ⟨fun X hX U hU => VaRTailAux.infConv_VaRL_eq ε hε0 α hα0 hα1 hX hU ρ hρm hρt,
    fun X hX U hU => VaRTailAux.optimal_alloc ε hε0 α hα0 hα1 hX hU ρ hρm hρt,
    fun X hX U hU => VaRTailAux.tendsto_VaRR ε hε0 α hα0 hα1 hX hU ρ hρm hρt,
    VaRTailAux.infConv_monetary _ ρ hρm, ?_, VaRTailAux.infConv_monetary _ ρ hρm, ?_⟩
  · intro X hX Y hY hXY
    obtain ⟨UX, hUX⟩ := exists_quantile_uniform P hP X hX
    obtain ⟨UY, hUY⟩ := exists_quantile_uniform P hP Y hY
    have t1 := VaRTailAux.tendsto_VaRR ε hε0 α hα0 hα1 hX hUX ρ hρm hρt
    have t2 := VaRTailAux.tendsto_VaRR ε hε0 α hα0 hα1 hY hUY ρ hρm hρt
    refine tendsto_nhds_unique (t1.congr' ?_) t2
    filter_upwards [Ioo_mem_nhdsGT hα0] with δ hδ
    have h := VaRTailAux.tail_cut ε hε0 α hα0 hα1 hX hY hUX hUY hXY δ hδ.1.le hδ.2
    exact congrArg (fun r : ℝ => (r : EReal))
      (hρt _ (VaRTailAux.cut_meas hX hUX ε _) _ (VaRTailAux.cut_meas hY hUY ε _) h)
  · intro X hX Y hY hXY
    obtain ⟨UX, hUX⟩ := exists_quantile_uniform P hP X hX
    obtain ⟨UY, hUY⟩ := exists_quantile_uniform P hP Y hY
    show TailRiskSharing.VaRConv.infConv TailRiskSharing.VaRConv.L0 ![TailRiskSharing.VaRConv.VaRL P α, ρ] X =
      TailRiskSharing.VaRConv.infConv TailRiskSharing.VaRConv.L0 ![TailRiskSharing.VaRConv.VaRL P α, ρ] Y
    rw [VaRTailAux.infConv_VaRL_eq ε hε0 α hα0 hα1 hX hUX ρ hρm hρt,
      VaRTailAux.infConv_VaRL_eq ε hε0 α hα0 hα1 hY hUY ρ hρm hρt]
    have h := VaRTailAux.tail_cut ε hε0 α hα0 hα1 hX hY hUX hUY hXY 0 le_rfl hα0
    simp only [sub_zero] at h
    rw [hρt _ (VaRTailAux.cut_meas hX hUX ε α) _ (VaRTailAux.cut_meas hY hUY ε α) h]
