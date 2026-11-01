-- Prove2me | solution 1 for TargetGranularity.SdVsMd.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:04:51.75249+00:00
-- url     : https://prove2.me/submissions/c6538192-a66f-485b-bb5e-a86e11576e9c

import Mathlib
import Definitions.Def_TargetGranularity_SdVsMd_Model

open TargetGranularity.SdVsMd MeasureTheory Set

/-- Superlevel sets of a convex continuous function on `[0,1]` are `[0,1]` minus an interval. -/
lemma tg_superlevel_lo (f : ℝ → ℝ) (c i0 : ℝ) (hconv : ConvexOn ℝ (Icc 0 1) f)
    (hcont : ContinuousOn f (Icc 0 1)) (hi0 : i0 ∈ Icc (0:ℝ) 1) (hfi0 : f i0 < c) :
    ∃ lo : ℝ, lo < i0 ∧ ∀ ω ∈ Icc (0:ℝ) 1, ω ≤ i0 → (c ≤ f ω ↔ ω ≤ lo) := by
  set L : Set ℝ := (Icc 0 1 ∩ f ⁻¹' Ici c) ∩ Iic i0 with hLdef
  have hLc : IsClosed L :=
    (hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici).inter isClosed_Iic
  have hLb : BddAbove L := ⟨i0, fun x hx => hx.2⟩
  by_cases hL : L.Nonempty
  · have hs := hLc.csSup_mem hL hLb
    have hsi : sSup L < i0 := by
      rcases lt_or_eq_of_le (show sSup L ≤ i0 from hs.2) with h | h
      · exact h
      · exfalso
        have := hs.1.2
        simp only [mem_preimage, mem_Ici] at this
        rw [h] at this; linarith
    refine ⟨sSup L, hsi, fun ω hω hωi => ⟨fun h => le_csSup hLb ⟨⟨hω, h⟩, hωi⟩, fun h => ?_⟩⟩
    by_contra hn
    push Not at hn
    have hseg : sSup L ∈ segment ℝ ω i0 := by
      rw [segment_eq_Icc (le_trans h hsi.le)]; exact ⟨h, hsi.le⟩
    have := hconv.le_on_segment hω hi0 hseg
    have h2 := hs.1.2
    simp only [mem_preimage, mem_Ici] at h2
    have : max (f ω) (f i0) < c := max_lt hn hfi0
    linarith
  · refine ⟨-1, by linarith [hi0.1], fun ω hω hωi => ⟨fun h => ?_, fun h => ?_⟩⟩
    · exact absurd ⟨ω, ⟨hω, h⟩, hωi⟩ hL
    · linarith [hω.1]

lemma tg_superlevel_hi (f : ℝ → ℝ) (c i0 : ℝ) (hconv : ConvexOn ℝ (Icc 0 1) f)
    (hcont : ContinuousOn f (Icc 0 1)) (hi0 : i0 ∈ Icc (0:ℝ) 1) (hfi0 : f i0 < c) :
    ∃ hi : ℝ, i0 < hi ∧ ∀ ω ∈ Icc (0:ℝ) 1, i0 ≤ ω → (c ≤ f ω ↔ hi ≤ ω) := by
  set R : Set ℝ := (Icc 0 1 ∩ f ⁻¹' Ici c) ∩ Ici i0 with hRdef
  have hRc : IsClosed R :=
    (hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici).inter isClosed_Ici
  have hRb : BddBelow R := ⟨i0, fun x hx => hx.2⟩
  by_cases hR : R.Nonempty
  · have hs := hRc.csInf_mem hR hRb
    have hsi : i0 < sInf R := by
      rcases lt_or_eq_of_le (show i0 ≤ sInf R from hs.2) with h | h
      · exact h
      · exfalso
        have := hs.1.2
        simp only [mem_preimage, mem_Ici] at this
        rw [← h] at this; linarith
    refine ⟨sInf R, hsi, fun ω hω hωi => ⟨fun h => csInf_le hRb ⟨⟨hω, h⟩, hωi⟩, fun h => ?_⟩⟩
    by_contra hn
    push Not at hn
    have hseg : sInf R ∈ segment ℝ i0 ω := by
      rw [segment_eq_Icc (le_trans hsi.le h)]; exact ⟨hsi.le, h⟩
    have := hconv.le_on_segment hi0 hω hseg
    have h2 := hs.1.2
    simp only [mem_preimage, mem_Ici] at h2
    have : max (f i0) (f ω) < c := max_lt hfi0 hn
    linarith
  · refine ⟨2, by linarith [hi0.2], fun ω hω hωi => ⟨fun h => ?_, fun h => ?_⟩⟩
    · exact absurd ⟨ω, ⟨hω, h⟩, hωi⟩ hR
    · linarith [hω.2]

lemma tg_superlevel (f : ℝ → ℝ) (c : ℝ) (hconv : ConvexOn ℝ (Icc 0 1) f)
    (hcont : ContinuousOn f (Icc 0 1)) :
    ∃ lo hi : ℝ, lo ≤ hi ∧
      {ω ∈ Icc (0:ℝ) 1 | c ≤ f ω} = {ω ∈ Icc (0:ℝ) 1 | ω ≤ lo ∨ hi ≤ ω} := by
  by_cases hI : ∃ i0 ∈ Icc (0:ℝ) 1, f i0 < c
  · obtain ⟨i0, hi0, hfi0⟩ := hI
    obtain ⟨lo, hlo, hL⟩ := tg_superlevel_lo f c i0 hconv hcont hi0 hfi0
    obtain ⟨hi, hhi, hR⟩ := tg_superlevel_hi f c i0 hconv hcont hi0 hfi0
    refine ⟨lo, hi, by linarith, ?_⟩
    ext ω
    simp only [mem_ofPred_eq]
    refine and_congr_right fun hω => ?_
    rcases le_total ω i0 with h | h
    · rw [hL ω hω h]
      constructor
      · exact Or.inl
      · rintro (h' | h')
        · exact h'
        · linarith
    · rw [hR ω hω h]
      constructor
      · exact Or.inr
      · rintro (h' | h')
        · linarith
        · exact h'
  · push Not at hI
    refine ⟨0, 0, le_rfl, ?_⟩
    ext ω
    simp only [mem_ofPred_eq]
    refine and_congr_right fun hω => ?_
    exact iff_of_true (hI ω hω) (le_total ω 0 |>.imp id id)

/-- The surplus integral is convex and continuous in `ω`. -/
lemma tg_integrand_integrable (p ω : ℝ) (E : Set (ℝ × ℝ)) (hE : E ⊆ unitSq) :
    IntegrableOn (fun x : ℝ × ℝ => max (util ω x.1 x.2 - p) 0) E := by
  have hK : IsCompact unitSq := isCompact_Icc.prod isCompact_Icc
  refine (ContinuousOn.integrableOn_compact hK ?_).mono_set hE
  apply Continuous.continuousOn
  unfold util; fun_prop

lemma tg_surplus_convex (p k : ℝ) (hk : 0 ≤ k) (E : Set (ℝ × ℝ)) (hE : E ⊆ unitSq) :
    ConvexOn ℝ (Icc 0 1)
      (fun ω => k * ∫ x in E, max (util ω x.1 x.2 - p) 0) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro ω₁ _ ω₂ _ a b ha hb hab
  simp only [smul_eq_mul]
  have h1 := tg_integrand_integrable p ω₁ E hE
  have h2 := tg_integrand_integrable p ω₂ E hE
  have hmono : ∫ x in E, max (util (a * ω₁ + b * ω₂) x.1 x.2 - p) 0 ≤
      ∫ x in E, (a * max (util ω₁ x.1 x.2 - p) 0 + b * max (util ω₂ x.1 x.2 - p) 0) := by
    apply integral_mono (tg_integrand_integrable p _ E hE)
      ((h1.const_mul a).add (h2.const_mul b))
    intro x
    simp only [util]
    have e : (a * ω₁ + b * ω₂) * x.1 + (1 - (a * ω₁ + b * ω₂)) * x.2 - p =
        a * (ω₁ * x.1 + (1 - ω₁) * x.2 - p) + b * (ω₂ * x.1 + (1 - ω₂) * x.2 - p) := by
      have : b = 1 - a := by linarith
      subst this; ring
    rw [e, Pi.add_apply]
    apply max_le
    · have := mul_le_mul_of_nonneg_left (le_max_left (ω₁ * x.1 + (1 - ω₁) * x.2 - p) 0) ha
      have := mul_le_mul_of_nonneg_left (le_max_left (ω₂ * x.1 + (1 - ω₂) * x.2 - p) 0) hb
      linarith
    · have := mul_nonneg ha (le_max_right (ω₁ * x.1 + (1 - ω₁) * x.2 - p) 0)
      have := mul_nonneg hb (le_max_right (ω₂ * x.1 + (1 - ω₂) * x.2 - p) 0)
      linarith
  rw [integral_add (h1.const_mul a) (h2.const_mul b), integral_const_mul,
    integral_const_mul] at hmono
  have := mul_le_mul_of_nonneg_left hmono hk
  nlinarith

lemma tg_surplus_cont (p k : ℝ) (E : Set (ℝ × ℝ)) (hEm : MeasurableSet E) (hE : E ⊆ unitSq) :
    ContinuousOn (fun ω => k * ∫ x in E, max (util ω x.1 x.2 - p) 0) (Icc 0 1) := by
  apply ContinuousOn.mul continuousOn_const
  have hfin : volume E ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono hE)
    rw [unitSq, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hfin
  apply continuousOn_of_dominated (bound := fun _ => 1 + |p|)
  · intro ω _
    apply Continuous.aestronglyMeasurable
    unfold util; fun_prop
  · intro ω hω
    apply ae_restrict_of_forall_mem hEm
    intro x hx
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hE hx
    obtain ⟨h5, h6⟩ := hω
    simp only [util, Real.norm_eq_abs]
    rw [abs_le]
    have : ω * x.1 + (1 - ω) * x.2 ≤ 1 := by nlinarith
    have : 0 ≤ ω * x.1 + (1 - ω) * x.2 := by nlinarith
    have := le_abs_self p
    have := neg_abs_le p
    constructor
    · have := le_max_right (ω * x.1 + (1 - ω) * x.2 - p) 0
      linarith [abs_nonneg p]
    · apply max_le <;> linarith [abs_nonneg p]
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro x
    apply Continuous.continuousOn
    unfold util; fun_prop

theorem solution (p cclick : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hcclick : 0 < cclick)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc 0 1)
    (hSpos : 0 < MeasureTheory.volume S) :
    ∃ ωlo ωhi : ℝ, ωlo ≤ ωhi ∧
      sdClick p cclick S = {ω ∈ Set.Icc (0 : ℝ) 1 | ω ≤ ωlo ∨ ωhi ≤ ω} := by
  have hE : S ×ˢ Icc (0:ℝ) 1 ⊆ unitSq := prod_mono hSsub subset_rfl
  have hEm : MeasurableSet (S ×ˢ Icc (0:ℝ) 1) := hS.prod measurableSet_Icc
  have hk : 0 ≤ (volume S).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  exact tg_superlevel (sdSurplus p S) cclick
    (tg_surplus_convex p _ hk _ hE) (tg_surplus_cont p _ _ hEm hE)
