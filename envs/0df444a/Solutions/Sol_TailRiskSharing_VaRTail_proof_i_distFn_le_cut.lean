-- Prove2me | solution 1 for TailRiskSharing.VaRTail.proof_i_distFn_le_cut
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T04:33:31.403753+00:00
-- url     : https://prove2.me/submissions/cd539ade-5a09-44ee-96a8-3f34fc6694c0

import Mathlib
import Definitions.Def_TailRiskSharing_VaRTail_Setting

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

open TailRiskSharing.VaRConv TailRiskSharing.VaRTail

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 - ε)
    (X : Ω → ℝ) (hX : X ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ))) (U : Ω → ℝ) (hU : IsQuantileUniform P X U)
    (Y : Ω → ℝ) (hY : Y ∈ (TailRiskSharing.VaRConv.L0 : Set (Ω → ℝ))) (hYvar : TailRiskSharing.VaRConv.VaRL P α Y = 0)
    (x : ℝ) (hx : TailRiskSharing.VaRConv.VaRR P (α + ε) X ≤ x) :
    TailRiskSharing.VaRConv.distFn P (X - Y) x ≤ TailRiskSharing.VaRConv.distFn P (cutAt P ε α X U) x :=
  VaRTailAux.distFn_le_cut ε hε0 α hα0 hα1 hX hU hY hYvar x hx
