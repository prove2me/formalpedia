-- Prove2me | solution 1 for PuhaWardFluid.Limit.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T10:46:10.931102+00:00
-- url     : https://prove2.me/submissions/3e7f0f95-cecf-4918-8a70-d6694896e0d7

import Mathlib
import Definitions.Def_PuhaWardFluid_Limit_Queue

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace PuhaWardFluid.Limit.L1aux

/-! ### A. Distribution functions -/

section A
variable (g : ℝ → ℝ≥0) (hg : Measurable g) (hfin : ∫⁻ x, (g x : ℝ≥0∞) ≤ 1)
  (hneg : ∀ x, x < 0 → g x = 0)
include hfin

lemma cdf_props : Monotone (cdf g) ∧ ∀ r, 0 ≤ cdf g r ∧ cdf g r ≤ 1 := by
  have hle : ∀ r, ∫⁻ y in Set.Icc 0 r, (g y : ℝ≥0∞) ≤ 1 := fun r =>
    (setLIntegral_le_lintegral _ _).trans hfin
  have hfin' : ∀ r, ∫⁻ y in Set.Icc 0 r, (g y : ℝ≥0∞) ≠ ⊤ := fun r =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (hle r)
  refine ⟨fun a b hab => ?_, fun r => ⟨ENNReal.toReal_nonneg, ?_⟩⟩
  · unfold cdf
    exact ENNReal.toReal_mono (hfin' b) (lintegral_mono_set (Set.Icc_subset_Icc le_rfl hab))
  · unfold cdf
    have := ENNReal.toReal_mono ENNReal.one_ne_top (hle r)
    simpa using this

include hg in
lemma integrable_g : Integrable (fun y => (g y : ℝ)) := by
  refine ⟨(NNReal.continuous_coe.measurable.comp hg).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have : ∀ y, ‖(g y : ℝ)‖ₑ = (g y : ℝ≥0∞) := fun y => by simp
  simp_rw [this]
  exact lt_of_le_of_lt hfin ENNReal.one_lt_top

include hg in
lemma cdf_eq_setIntegral (x : ℝ) : cdf g x = ∫ y in Set.Icc 0 x, (g y : ℝ) := by
  unfold cdf
  have h := integral_toReal (μ := volume.restrict (Set.Icc 0 x)) (f := fun y => (g y : ℝ≥0∞))
    ((measurable_coe_nnreal_ennreal.comp hg).aemeasurable)
    (Eventually.of_forall fun _ => ENNReal.coe_lt_top)
  simp only [ENNReal.coe_toReal] at h
  exact h.symm

include hg hneg in
lemma cdf_eq_primitive (x : ℝ) : cdf g x = ∫ y in (0 : ℝ)..x, (g y : ℝ) := by
  rw [cdf_eq_setIntegral g hg hfin]
  rcases le_or_gt 0 x with hx | hx
  · rw [intervalIntegral.integral_of_le hx, integral_Icc_eq_integral_Ioc]
  · rw [Set.Icc_eq_empty (not_le.2 hx), intervalIntegral.integral_symm,
      intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))
        (fun y hy => by simp [hneg y hy.2])]
    simp

include hg hneg in
lemma cdf_cont : Continuous (cdf g) := by
  have : cdf g = fun x => ∫ y in (0 : ℝ)..x, (g y : ℝ) := funext (cdf_eq_primitive g hg hfin hneg)
  rw [this]
  exact intervalIntegral.continuous_primitive
    (fun a b => (integrable_g g hg hfin).intervalIntegrable) 0

lemma cdf_zero : cdf g 0 = 0 := by
  unfold cdf
  rw [Set.Icc_self, Measure.restrict_singleton]
  simp

include hg hneg in
lemma edge_pos : 0 < edge g := by
  have hc := (cdf_cont g hg hfin hneg).continuousAt (x := 0)
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, h⟩ := hc (1 / 2) (by norm_num)
  have h1 : cdf g (δ / 2) < 1 := by
    have := h (x := δ / 2) (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
    rw [cdf_zero g hfin, Real.dist_eq, sub_zero] at this
    linarith [le_abs_self (cdf g (δ / 2))]
  unfold edge
  refine lt_of_lt_of_le ?_ (le_iSup₂ (f := fun (x : ℝ) (_ : 0 ≤ x ∧ cdf g x < 1) =>
    ENNReal.ofReal x) (δ / 2) ⟨by linarith, h1⟩)
  simp; linarith

lemma cdf_lt_one_of_lt_edge (y : ℝ) (hy : ENNReal.ofReal y < edge g) : cdf g y < 1 := by
  obtain ⟨hmono, -⟩ := cdf_props g hfin
  unfold edge at hy
  obtain ⟨x, hx⟩ := lt_iSup_iff.1 hy
  obtain ⟨⟨hx0, hx1⟩, hx2⟩ := lt_iSup_iff.1 hx
  have : y < x := by
    by_contra hcon
    push_neg at hcon
    exact absurd hx2 (not_lt.2 (ENNReal.ofReal_le_ofReal hcon))
  exact lt_of_le_of_lt (hmono this.le) hx1

include hg hneg in
lemma cdf_edge_eq_one (hH : edge g ≠ ⊤) : cdf g (edge g).toReal = 1 := by
  obtain ⟨hmono, h01⟩ := cdf_props g hfin
  set H := (edge g).toReal with hHdef
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
  have hgt : ∀ x, H < x → cdf g x = 1 := by
    intro x hx
    refine le_antisymm (h01 x).2 ?_
    by_contra hlt
    push_neg at hlt
    have : ENNReal.ofReal x ≤ edge g :=
      le_iSup₂ (f := fun (x : ℝ) (_ : 0 ≤ x ∧ cdf g x < 1) => ENNReal.ofReal x) x
        ⟨by linarith, hlt⟩
    rw [← ENNReal.ofReal_toReal hH, ENNReal.ofReal_le_ofReal_iff hH0] at this
    linarith
  have hT : Tendsto (cdf g) (𝓝[>] H) (𝓝 (cdf g H)) :=
    ((cdf_cont g hg hfin hneg).tendsto H).mono_left nhdsWithin_le_nhds
  have hT1 : Tendsto (cdf g) (𝓝[>] H) (𝓝 1) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x hx => (hgt x hx).symm)
  exact tendsto_nhds_unique hT hT1

end A

/-! ### B. Residual times -/

section B
variable (g : ℝ → ℝ≥0) (hg : Measurable g) (hfin : ∫⁻ x, (g x : ℝ≥0∞) ≤ 1)
  (hneg : ∀ x, x < 0 → g x = 0)
include hg hfin hneg

lemma condCdf_cont (y : ℝ) : Continuous (fun t => condCdf g y t) := by
  unfold condCdf
  exact (((cdf_cont g hg hfin hneg).comp (continuous_id.add continuous_const)).sub
    continuous_const).div_const _

lemma resid_pos (y u : ℝ) (hu : 0 < u) : 0 < QueueSeq.resid g y u := by
  have hc := (condCdf_cont g hg hfin hneg y).continuousAt (x := 0)
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, h⟩ := hc u hu
  have h0 : condCdf g y 0 = 0 := by unfold condCdf; simp
  unfold QueueSeq.resid
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.2 hδ) (le_iInf₂ fun t ht => ?_)
  apply ENNReal.ofReal_le_ofReal
  by_contra hlt
  push_neg at hlt
  have := h (x := t) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]; exact hlt)
  rw [h0, Real.dist_eq, sub_zero] at this
  linarith [le_abs_self (condCdf g y t), ht.2]

lemma resid_lt (y u : ℝ) (hy0 : 0 ≤ y) (hyH : ENNReal.ofReal y < edge g) (hu1 : u < 1) :
    QueueSeq.resid g y u = ⊤ ∨
      ENNReal.ofReal ((QueueSeq.resid g y u).toReal + y) < edge g := by
  by_cases hH : edge g = ⊤
  · right; rw [hH]; exact ENNReal.ofReal_lt_top
  right
  obtain ⟨hmono, h01⟩ := cdf_props g hfin
  set H := (edge g).toReal with hHdef
  have hyH' : y < H := by
    rw [← ENNReal.ofReal_toReal hH] at hyH
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hy0).1 hyH
  have hcy : cdf g y < 1 := cdf_lt_one_of_lt_edge g hfin y hyH
  have hval : condCdf g y (H - y) = 1 := by
    unfold condCdf
    rw [sub_add_cancel, cdf_edge_eq_one g hg hfin hneg hH]
    exact div_self (by linarith)
  have hc := (condCdf_cont g hg hfin hneg y).continuousAt (x := H - y)
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, h⟩ := hc (1 - u) (by linarith)
  set t' := max ((H - y) - δ / 2) ((H - y) / 2) with ht'
  have ht'pos : 0 < t' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have ht'lt : t' < H - y := max_lt (by linarith) (by linarith)
  have ht'u : u < condCdf g y t' := by
    have := h (x := t') (by
      rw [Real.dist_eq, abs_lt]; constructor
      · linarith [le_max_left ((H - y) - δ / 2) ((H - y) / 2)]
      · linarith)
    rw [hval, Real.dist_eq, abs_lt] at this
    linarith [this.1]
  have hle : QueueSeq.resid g y u ≤ ENNReal.ofReal t' := by
    unfold QueueSeq.resid
    exact iInf₂_le t' ⟨ht'pos, ht'u⟩
  have hne : QueueSeq.resid g y u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hle' : (QueueSeq.resid g y u).toReal ≤ t' := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal ht'pos.le] at this
  rw [← ENNReal.ofReal_toReal hH]
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)

end B

/-! ### C. Laws -/

section C
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (g : ℝ → ℝ≥0) (hg : Measurable g) (hfin : ∫⁻ x, (g x : ℝ≥0∞) ≤ 1)
  (hneg : ∀ x, x < 0 → g x = 0)
include hg hfin hneg

lemma tail_null (S : Set Ω) (hH : edge g ≠ ⊤)
    (hS : ∀ x, 0 < x → ENNReal.ofReal x < edge g → P S ≤ 1 - ENNReal.ofReal (cdf g x)) :
    P S = 0 := by
  set H := (edge g).toReal with hHdef
  have hHpos : 0 < H := ENNReal.toReal_pos (edge_pos g hg hfin hneg).ne' hH
  have hT : Tendsto (fun x => 1 - ENNReal.ofReal (cdf g x)) (𝓝[<] H) (𝓝 0) := by
    have h1 : Tendsto (fun x => ENNReal.ofReal (cdf g x)) (𝓝[<] H) (𝓝 1) := by
      have := ((ENNReal.continuous_ofReal.comp (cdf_cont g hg hfin hneg)).tendsto H).mono_left
        (nhdsWithin_le_nhds (s := Set.Iio H))
      have he : cdf g H = 1 := cdf_edge_eq_one g hg hfin hneg hH
      simpa [Function.comp_def, he] using this
    have h2 := ((ENNReal.continuous_sub_left ENNReal.one_ne_top).tendsto 1).comp h1
    simpa [Function.comp_def] using h2
  refine le_antisymm (ge_of_tendsto hT ?_) bot_le
  filter_upwards [Ioo_mem_nhdsLT hHpos] with x hx
  refine hS x hx.1 ?_
  rw [← ENNReal.ofReal_toReal hH]
  exact (ENNReal.ofReal_lt_ofReal_iff hHpos).2 hx.2

lemma ae_real_law (X : Ω → ℝ) (hX : Measurable X)
    (hlaw : ∀ x : ℝ, 0 ≤ x → P {ω | X ω ≤ x} = ENNReal.ofReal (cdf g x)) :
    ∀ᵐ ω ∂P, 0 ≤ X ω ∧ ENNReal.ofReal (X ω) < edge g := by
  have h1 : ∀ᵐ ω ∂P, 0 ≤ X ω := by
    rw [ae_iff]
    refine measure_mono_null (t := {ω | X ω ≤ 0}) (fun ω hω => ?_) ?_
    · simp only [Set.mem_setOf_eq, not_le] at hω ⊢; exact hω.le
    · rw [hlaw 0 le_rfl, cdf_zero g hfin]; simp
  have h2 : ∀ᵐ ω ∂P, ENNReal.ofReal (X ω) < edge g := by
    by_cases hH : edge g = ⊤
    · exact Eventually.of_forall fun ω => by rw [hH]; exact ENNReal.ofReal_lt_top
    rw [ae_iff]
    refine tail_null P g hg hfin hneg _ hH fun x hx hxH => ?_
    have hsub : {ω | ¬ENNReal.ofReal (X ω) < edge g} ⊆ {ω | X ω ≤ x}ᶜ := by
      intro ω hω
      simp only [Set.mem_setOf_eq, not_lt, Set.mem_compl_iff, not_le] at hω ⊢
      exact (ENNReal.ofReal_lt_ofReal_iff'.1 (lt_of_lt_of_le hxH hω)).1
    calc P _ ≤ P {ω | X ω ≤ x}ᶜ := measure_mono hsub
      _ = 1 - ENNReal.ofReal (cdf g x) := by
        rw [prob_compl_eq_one_sub (measurableSet_le hX measurable_const), hlaw x hx.le]
  filter_upwards [h1, h2] with ω h1 h2 using ⟨h1, h2⟩

lemma ae_ennreal_law (X : Ω → ℝ≥0∞) (hX : Measurable X)
    (hlaw : ∀ x : ℝ, 0 ≤ x → P {ω | X ω ≤ ENNReal.ofReal x} = ENNReal.ofReal (cdf g x)) :
    ∀ᵐ ω ∂P, X ω = ⊤ ∨ ENNReal.ofReal (X ω).toReal < edge g := by
  by_cases hH : edge g = ⊤
  · exact Eventually.of_forall fun ω => Or.inr (by rw [hH]; exact ENNReal.ofReal_lt_top)
  rw [ae_iff]
  refine tail_null P g hg hfin hneg _ hH fun x hx hxH => ?_
  have hsub : {ω | ¬(X ω = ⊤ ∨ ENNReal.ofReal (X ω).toReal < edge g)} ⊆
      {ω | X ω ≤ ENNReal.ofReal x}ᶜ := by
    intro ω hω
    simp only [Set.mem_setOf_eq, not_or, not_lt, Set.mem_compl_iff, not_le] at hω ⊢
    rw [ENNReal.ofReal_toReal hω.1] at hω
    exact lt_of_lt_of_le hxH hω.2
  calc P _ ≤ P {ω | X ω ≤ ENNReal.ofReal x}ᶜ := measure_mono hsub
    _ = 1 - ENNReal.ofReal (cdf g x) := by
      rw [prob_compl_eq_one_sub (measurableSet_le hX measurable_const), hlaw x hx.le]

end C

lemma ae_unif {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (hX : Measurable X)
    (h : P.map X = unif01) : ∀ᵐ ω ∂P, X ω ∈ Set.Ioo (0 : ℝ) 1 := by
  have : ∀ᵐ x ∂(P.map X), x ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [h, unif01]; exact ae_restrict_mem measurableSet_Ioo
  exact ae_of_ae_map hX.aemeasurable this

/-! ### D. Arrival times -/

lemma inf_le_iff (E : ℝ≥0 → ℕ) (hmono : Monotone E) (hcad : IsCadlag E) (n : ℕ) (s : ℝ≥0) :
    (⨅ (t : ℝ≥0) (_ : n ≤ E t), (t : ℝ≥0∞)) ≤ (s : ℝ≥0∞) ↔ n ≤ E s := by
  constructor
  · intro hle
    have hrc := hcad.1 s
    have hev : ∀ᶠ t in 𝓝[≥] s, E t = E s :=
      hrc.tendsto (isOpen_discrete {E s} |>.mem_nhds rfl)
    obtain ⟨ε, hε, hεs⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 hev
    have hε' : s < ε := hε
    have hlt : (⨅ (t : ℝ≥0) (_ : n ≤ E t), (t : ℝ≥0∞)) < (ε : ℝ≥0∞) :=
      lt_of_le_of_lt hle (by exact_mod_cast hε')
    rw [iInf_lt_iff] at hlt
    obtain ⟨t, ht⟩ := hlt
    rw [iInf_lt_iff] at ht
    obtain ⟨hnt, htε⟩ := ht
    have htε' : t < ε := by exact_mod_cast htε
    rcases le_or_gt t s with hts | hts
    · exact hnt.trans (hmono hts)
    · have : E t = E s := hεs ⟨hts.le, htε'⟩
      rw [← this]; exact hnt
  · intro h
    exact iInf₂_le s h


/-! ### E. One customer -/

section E
variable {H : ℝ≥0∞} {f f' : ℝ → ℝ}

/-- The real-valued contribution of a customer with entry time `κ` and service time `V`. -/
noncomputable def ind (g : ℝ → ℝ) (κ V s : ℝ) : ℝ :=
  if 0 ≤ s - κ ∧ s - κ < V then g (s - κ) else 0

lemma ind_eq_indicator (g : ℝ → ℝ) (κ V : ℝ) :
    ind g κ V = (Set.Ico κ (κ + V)).indicator (fun u => g (u - κ)) := by
  funext u
  unfold ind
  by_cases h : 0 ≤ u - κ ∧ u - κ < V
  · rw [if_pos h, Set.indicator_of_mem]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · rw [if_neg h, Set.indicator_of_notMem]
    intro hu
    exact h ⟨by linarith [hu.1], by linarith [hu.2]⟩

lemma ftc (hf : IsC1c H f f') (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q)
    (hq : ENNReal.ofReal q < H) : ∫ x in p..q, f' x = f q - f p := by
  obtain ⟨hcont, hder, hcont', -⟩ := hf
  have hsub : Set.Icc p q ⊆ {x | 0 ≤ x ∧ ENNReal.ofReal x < H} := fun x hx =>
    ⟨hp.trans hx.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hx.2) hq⟩
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hpq (hcont.mono hsub)
  · intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt hp hx.1
    exact (hder x hx0.le (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hx.2.le) hq)).mono
      (Set.Ioi_subset_Ici_self.trans (Set.Ici_subset_Ici.2 hx0.le))
  · exact (hcont'.mono hsub).intervalIntegrable_of_Icc hpq

lemma ind_integrable (hf : IsC1c H f f') (κ V : ℝ) (hV0 : 0 ≤ V)
    (hVH : ENNReal.ofReal V < H) : Integrable (ind f' κ V) := by
  rw [ind_eq_indicator, integrable_indicator_iff measurableSet_Ico]
  refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set Set.Ico_subset_Icc_self
  have hc := hf.2.2.1
  refine hc.comp (continuous_id.sub continuous_const).continuousOn fun u hu => ?_
  refine ⟨by linarith [hu.1], lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hVH⟩
  linarith [hu.2]

lemma ae_eq_Ioc_of_sandwich {A : Set ℝ} {a b : ℝ} (h1 : Set.Ioo a b ⊆ A)
    (h2 : A ⊆ Set.Icc a b) : A =ᵐ[volume] Set.Ioc a b := by
  refine Filter.EventuallyLE.antisymm ?_ ?_
  · exact h2.eventuallyLE.trans Ioc_ae_eq_Icc.symm.le
  · exact Ioo_ae_eq_Ioc.symm.le.trans h1.eventuallyLE

lemma int_ind (hf : IsC1c H f f') (κ V t : ℝ) (hVH : ENNReal.ofReal V < H) :
    ∫ u in Set.Icc 0 t, ind f' κ V u =
      if max 0 κ ≤ min t (κ + V) then f (min t (κ + V) - κ) - f (max 0 κ - κ) else 0 := by
  rw [ind_eq_indicator, integral_indicator measurableSet_Ico, Measure.restrict_restrict
    measurableSet_Ico]
  set lo := max 0 κ
  set hi := min t (κ + V)
  have h2 : Set.Ico κ (κ + V) ∩ Set.Icc 0 t ⊆ Set.Icc lo hi := fun u hu =>
    ⟨max_le hu.2.1 hu.1.1, le_min hu.2.2 hu.1.2.le⟩
  split_ifs with hle
  · have h1 : Set.Ioo lo hi ⊆ Set.Ico κ (κ + V) ∩ Set.Icc 0 t := fun u hu => by
      have := hu.1; have := hu.2
      refine ⟨⟨by linarith [le_max_right 0 κ], by linarith [min_le_right t (κ + V)]⟩,
        by linarith [le_max_left 0 κ], by linarith [min_le_left t (κ + V)]⟩
    rw [setIntegral_congr_set (ae_eq_Ioc_of_sandwich h1 h2), ← intervalIntegral.integral_of_le hle,
      intervalIntegral.integral_comp_sub_right (fun x => f' x)]
    refine ftc hf _ _ (by linarith [le_max_right 0 κ]) (by linarith) ?_
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by linarith [min_le_right t (κ + V)])) hVH
  · have : Set.Ico κ (κ + V) ∩ Set.Icc 0 t = ∅ := by
      refine Set.eq_empty_of_subset_empty (h2.trans ?_)
      rw [Set.Icc_eq_empty hle]
    rw [this]; simp

lemma cust_real (hf : IsC1c H f f') (κ V t : ℝ) (ht : 0 ≤ t) (hV0 : 0 ≤ V)
    (hVH : ENNReal.ofReal V < H) (hC : κ ≤ 0 → -κ < V) :
    ind f κ V t = ind f κ V 0 + (∫ u in Set.Icc 0 t, ind f' κ V u)
      - (if κ + V ≤ t then f V else 0) + (if 0 < κ ∧ κ ≤ t then f 0 else 0) := by
  rw [int_ind hf κ V t hVH]
  unfold ind
  rcases le_or_gt κ 0 with hκ | hκ
  · have hCV := hC hκ
    rw [max_eq_left hκ]
    have c2 : 0 ≤ (0:ℝ) - κ ∧ (0:ℝ) - κ < V := ⟨by linarith, by linarith⟩
    have c5 : ¬(0 < κ ∧ κ ≤ t) := fun h => by linarith [h.1]
    rw [if_pos c2, if_neg c5]
    rcases lt_or_ge t (κ + V) with htV | htV
    · have c1 : 0 ≤ t - κ ∧ t - κ < V := ⟨by linarith, by linarith⟩
      have c4 : ¬ κ + V ≤ t := by linarith
      rw [min_eq_left htV.le, if_pos c1, if_pos ht, if_neg c4]
      ring
    · have c1 : ¬(0 ≤ t - κ ∧ t - κ < V) := fun h => by linarith [h.2]
      have c3 : (0:ℝ) ≤ κ + V := by linarith
      rw [min_eq_right htV, if_neg c1, if_pos c3, if_pos htV]
      simp only [add_sub_cancel_left]
      ring
  · have c2 : ¬(0 ≤ (0:ℝ) - κ ∧ (0:ℝ) - κ < V) := fun h => by linarith [h.1]
    rw [max_eq_right hκ.le, if_neg c2]
    rcases lt_or_ge t κ with htk | htk
    · have c1 : ¬(0 ≤ t - κ ∧ t - κ < V) := fun h => by linarith [h.1]
      have c3 : ¬ κ ≤ min t (κ + V) := fun h => by linarith [min_le_left t (κ + V)]
      have c4 : ¬ κ + V ≤ t := by linarith
      have c5 : ¬(0 < κ ∧ κ ≤ t) := fun h => by linarith [h.2]
      rw [if_neg c1, if_neg c3, if_neg c4, if_neg c5]
      ring
    have c5 : 0 < κ ∧ κ ≤ t := ⟨hκ, htk⟩
    rcases lt_or_ge t (κ + V) with htV | htV
    · have c1 : 0 ≤ t - κ ∧ t - κ < V := ⟨by linarith, by linarith⟩
      have c4 : ¬ κ + V ≤ t := by linarith
      rw [min_eq_left htV.le, if_pos c1, if_pos htk, if_neg c4, if_pos c5]
      simp only [sub_self]
      ring
    · have c1 : ¬(0 ≤ t - κ ∧ t - κ < V) := fun h => by linarith [h.2]
      have c3 : κ ≤ κ + V := by linarith
      rw [min_eq_right htV, if_neg c1, if_pos c3, if_pos htV, if_pos c5]
      simp only [add_sub_cancel_left, sub_self]
      ring

end E


/-! ### E2. Atoms and EReal bookkeeping -/

section E2
variable {H : ℝ≥0∞}

lemma atom_coe (z : EReal) :
    (atomAt H z : Measure (Iv H)) =
      if h : z ≠ ⊤ ∧ ((z.toReal.toNNReal : ℝ≥0) : ℝ≥0∞) < H then
        Measure.dirac (⟨z.toReal.toNNReal, h.2⟩ : Iv H) else 0 := by
  by_cases h : z ≠ ⊤ ∧ ((z.toReal.toNNReal : ℝ≥0) : ℝ≥0∞) < H
  · rw [dif_pos h]
    have : atomAt H z = ⟨Measure.dirac (⟨z.toReal.toNNReal, h.2⟩ : Iv H), inferInstance⟩ := by
      unfold atomAt; exact dif_pos h
    rw [this]; rfl
  · rw [dif_neg h]
    have : atomAt H z = 0 := by
      unfold atomAt; exact dif_neg h
    rw [this]; rfl

lemma pair_atom (f : ℝ → ℝ) (z : EReal) :
    pair f (atomAt H z) =
      if z ≠ ⊤ ∧ ((z.toReal.toNNReal : ℝ≥0) : ℝ≥0∞) < H then f (z.toReal.toNNReal : ℝ) else 0 := by
  unfold pair
  rw [atom_coe]
  by_cases h : z ≠ ⊤ ∧ ((z.toReal.toNNReal : ℝ≥0) : ℝ≥0∞) < H
  · rw [dif_pos h, if_pos h, integral_dirac]
  · rw [dif_neg h, if_neg h]
    simp

lemma integrable_atom (f : ℝ → ℝ) (z : EReal) :
    Integrable (fun x : Iv H => f ((x : ℝ≥0) : ℝ)) (atomAt H z : Measure (Iv H)) := by
  rw [atom_coe]
  by_cases h : z ≠ ⊤ ∧ ((z.toReal.toNNReal : ℝ≥0) : ℝ≥0∞) < H
  · rw [dif_pos h]
    exact integrable_dirac (by exact enorm_lt_top)
  · rw [dif_neg h]
    simp

lemma pair_sum {ι : Type*} (s : Finset ι) (ν : ι → FiniteMeasure (Iv H)) (f : ℝ → ℝ)
    (hν : ∀ i ∈ s, Integrable (fun x : Iv H => f ((x : ℝ≥0) : ℝ)) (ν i : Measure (Iv H))) :
    pair f (∑ i ∈ s, ν i) = ∑ i ∈ s, pair f (ν i) := by
  unfold pair
  rw [FiniteMeasure.toMeasure_sum, integral_finsetSum_measure hν]

lemma pair_zero (f : ℝ → ℝ) : pair f (0 : FiniteMeasure (Iv H)) = 0 := by
  simp [pair]

open Classical in
/-- The contribution of one customer, as it appears in the measure-valued state. -/
noncomputable def Tm (H : ℝ≥0∞) (g : ℝ → ℝ) (k v : EReal) (s : ℝ) : ℝ :=
  pair g (if 0 ≤ (s : EReal) - k ∧ (s : EReal) - k < v then
    atomAt H (min (max ((s : EReal) - k) 0) v) else 0)

lemma Tm_real (g : ℝ → ℝ) (κ V s : ℝ) (hVH : ENNReal.ofReal V < H) :
    Tm H g κ V s = ind g κ V s := by
  unfold Tm ind
  rw [← EReal.coe_sub]
  by_cases hc : 0 ≤ s - κ ∧ s - κ < V
  · have hc' : (0 : EReal) ≤ ((s - κ : ℝ) : EReal) ∧ ((s - κ : ℝ) : EReal) < (V : EReal) :=
      ⟨EReal.coe_nonneg.2 hc.1, EReal.coe_lt_coe_iff.2 hc.2⟩
    rw [if_pos hc', if_pos hc, max_eq_left hc'.1, min_eq_left hc'.2.le, pair_atom]
    have hH : ((((s - κ : ℝ) : EReal).toReal.toNNReal : ℝ≥0) : ℝ≥0∞) < H := by
      rw [EReal.toReal_coe]
      exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hc.2.le) hVH
    rw [if_pos ⟨EReal.coe_ne_top _, hH⟩, EReal.toReal_coe, Real.coe_toNNReal _ hc.1]
  · have hc' : ¬((0 : EReal) ≤ ((s - κ : ℝ) : EReal) ∧ ((s - κ : ℝ) : EReal) < (V : EReal)) := by
      rw [EReal.coe_nonneg, EReal.coe_lt_coe_iff]; exact hc
    rw [if_neg hc', if_neg hc, pair_zero]

lemma Tm_top (g : ℝ → ℝ) (m V' : ℝ) (hg0 : ∀ x, m < x → ENNReal.ofReal x < H → g x = 0)
    (hmV : m < V') (hV'H : ENNReal.ofReal V' < H) (κ s : ℝ) :
    Tm H g κ ⊤ s = ind g κ V' s := by
  unfold Tm ind
  rw [← EReal.coe_sub]
  by_cases h0 : 0 ≤ s - κ
  · have hc' : (0 : EReal) ≤ ((s - κ : ℝ) : EReal) ∧ ((s - κ : ℝ) : EReal) < ⊤ :=
      ⟨EReal.coe_nonneg.2 h0, EReal.coe_lt_top _⟩
    rw [if_pos hc', max_eq_left hc'.1, min_eq_left le_top, pair_atom, EReal.toReal_coe,
      Real.coe_toNNReal _ h0]
    by_cases hV : s - κ < V'
    · have ha : ((s - κ : ℝ) : EReal) ≠ ⊤ ∧ (((s - κ).toNNReal : ℝ≥0) : ℝ≥0∞) < H :=
        ⟨EReal.coe_ne_top _, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hV.le) hV'H⟩
      rw [if_pos ha, if_pos (show 0 ≤ s - κ ∧ s - κ < V' from ⟨h0, hV⟩)]
    · rw [if_neg (show ¬(0 ≤ s - κ ∧ s - κ < V') from fun h => hV h.2)]
      split_ifs with hH
      · exact hg0 _ (by linarith [not_lt.1 hV]) hH.2
      · rfl
  · rw [if_neg (fun h => h0 (EReal.coe_nonneg.1 h.1)), if_neg (fun h => h0 h.1), pair_zero]

lemma ite_coe_iff {α : Type*} (p q : Prop) [Decidable p] [Decidable q] (h : p ↔ q) (a b : α) :
    (if p then a else b) = (if q then a else b) := by
  by_cases hq : q
  · rw [if_pos (h.2 hq), if_pos hq]
  · rw [if_neg (fun hp => hq (h.1 hp)), if_neg hq]

lemma cust {f f' : ℝ → ℝ} (hf : IsC1c H f f') (k v : EReal) (hk : k ≠ ⊥)
    (hB : v = ⊤ ∨ ∃ V : ℝ, v = V ∧ 0 ≤ V ∧ ENNReal.ofReal V < H)
    (hC : k ≤ 0 → -k < v ∧ ENNReal.ofReal (-k.toReal) < H) (t : ℝ) (ht : 0 ≤ t) :
    (Tm H f k v t = Tm H f k v 0 + (∫ u in Set.Icc 0 t, Tm H f' k v u)
      - (if k + v ≤ (t : EReal) then f v.toReal else 0)
      + (if 0 < k ∧ k ≤ (t : EReal) then f 0 else 0)) ∧
    IntegrableOn (Tm H f' k v) (Set.Icc 0 t) := by
  induction k using EReal.rec with
  | bot => exact absurd rfl hk
  | top =>
    have hz : ∀ (g : ℝ → ℝ) (s : ℝ), Tm H g ⊤ v s = 0 := fun g s => by
      unfold Tm
      rw [if_neg, pair_zero]
      rintro ⟨h, -⟩
      simp at h
    have hv : v ≠ ⊥ := by rcases hB with h | ⟨V, h, -⟩ <;> simp [h]
    have hz' : ∀ (g : ℝ → ℝ), Tm H g ⊤ v = fun _ => 0 := fun g => funext (hz g)
    rw [hz' f, hz' f']
    refine ⟨?_, integrableOn_const (by simp)⟩
    rw [if_neg, if_neg]
    · simp
    · rintro ⟨-, h⟩; simp at h
    · rw [EReal.top_add_of_ne_bot hv]; simp
  | coe κ =>
    have hent : (if 0 < (κ : EReal) ∧ (κ : EReal) ≤ (t : EReal) then f 0 else 0) =
        (if 0 < κ ∧ κ ≤ t then f 0 else 0) :=
      ite_coe_iff _ _ (by rw [EReal.coe_pos, EReal.coe_le_coe_iff]) _ _
    rw [hent]
    rcases hB with rfl | ⟨V, rfl, hV0, hVH⟩
    · obtain ⟨m, hm0, hmH, hvan⟩ := hf.2.2.2
      have hM : ENNReal.ofReal (max m (-κ)) < H := by
        rw [ENNReal.ofReal_max]
        refine max_lt hmH ?_
        rcases le_or_gt κ 0 with hκ | hκ
        · have := (hC (by exact_mod_cast hκ)).2
          simpa using this
        · rw [ENNReal.ofReal_of_nonpos (by linarith)]
          exact lt_of_le_of_lt bot_le hmH
      obtain ⟨V', hV'0, hMV', hV'H⟩ := ENNReal.lt_iff_exists_real_btwn.1 hM
      have hMV : max m (-κ) < V' := (ENNReal.ofReal_lt_ofReal_iff'.1 hMV').1
      have hmV : m < V' := lt_of_le_of_lt (le_max_left _ _) hMV
      have hfV : Tm H f κ ⊤ = ind f κ V' :=
        funext (Tm_top f m V' (fun x hx hxH => (hvan x hx hxH).1) hmV hV'H κ)
      have hf'V : Tm H f' κ ⊤ = ind f' κ V' :=
        funext (Tm_top f' m V' (fun x hx hxH => (hvan x hx hxH).2) hmV hV'H κ)
      rw [hfV, hf'V]
      have hdep : ¬ ((κ : EReal) + ⊤ ≤ (t : EReal)) := by
        rw [EReal.coe_add_top]; simp
      rw [if_neg hdep]
      have key := cust_real hf κ V' t ht hV'0 hV'H
        (fun _ => by linarith [le_max_right m (-κ)])
      have hfV' : f V' = 0 := (hvan V' hmV hV'H).1
      rw [hfV', ite_self] at key
      refine ⟨by linarith [key], (ind_integrable hf κ V' hV'0 hV'H).integrableOn⟩
    · have hfV : ∀ (g : ℝ → ℝ), Tm H g κ V = ind g κ V := fun g =>
        funext fun s => Tm_real g κ V s hVH
      rw [hfV f, hfV f']
      have hdep : (if (κ : EReal) + (V : EReal) ≤ (t : EReal) then f (V : EReal).toReal else 0) =
          (if κ + V ≤ t then f V else 0) := by
        rw [EReal.toReal_coe]
        exact ite_coe_iff _ _ (by rw [← EReal.coe_add, EReal.coe_le_coe_iff]) _ _
      rw [hdep]
      have key := cust_real hf κ V t ht hV0 hVH (fun hκ => by
        have := (hC (by exact_mod_cast hκ)).1
        rw [← EReal.coe_neg] at this
        exact EReal.coe_lt_coe_iff.1 this)
      exact ⟨key, (ind_integrable hf κ V hV0 hVH).integrableOn⟩

end E2


/-! ### F. Summing over customers -/

section F
variable {H : ℝ≥0∞}

lemma not_nonneg_sub_of_lt (a : ℝ) (k : EReal) (h : (a : EReal) < k) : ¬ (0 ≤ (a : EReal) - k) := by
  induction k using EReal.rec with
  | bot => exact absurd h (not_lt_bot)
  | top => simp
  | coe κ =>
    rw [← EReal.coe_sub, EReal.coe_nonneg, not_le]
    have := EReal.coe_lt_coe_iff.1 h
    linarith

open Classical in
lemma generic1 {f f' : ℝ → ℝ} (hf : IsC1c H f f') (c : ℕ) (E : ℝ≥0 → ℕ) (hE : Monotone E)
    (k v : ℤ → EReal) (μ : ℝ≥0 → FiniteMeasure (Iv H))
    (hμ : ∀ s, μ s = ∑ i ∈ Finset.Ioc (-(c : ℤ)) (E s : ℤ),
      if 0 ≤ ((s : ℝ) : EReal) - k i ∧ ((s : ℝ) : EReal) - k i < v i
      then atomAt H (min (max (((s : ℝ) : EReal) - k i) 0) (v i)) else 0)
    (hA : ∀ i, -(c : ℤ) < i → k i ≠ ⊥)
    (hB : ∀ i, -(c : ℤ) < i → v i = ⊤ ∨ ∃ V : ℝ, v i = V ∧ 0 ≤ V ∧ ENNReal.ofReal V < H)
    (hC : ∀ i, -(c : ℤ) < i → k i ≤ 0 → -k i < v i ∧ ENNReal.ofReal (-(k i).toReal) < H)
    (hD : ∀ (s : ℝ≥0) (i : ℤ), (E s : ℤ) < i → ((s : ℝ) : EReal) < k i) (t : ℝ≥0) :
    pair f (μ t) = pair f (μ 0) + (∫ u in Set.Icc (0 : ℝ) t, pair f' (μ u.toNNReal))
      - ∑ i ∈ (Finset.Ioc (-(c : ℤ)) (E t : ℤ)).filter (fun i => k i + v i ≤ ((t : ℝ) : EReal)),
          f (v i).toReal
      + f 0 * ((((Finset.Ioc (-(c : ℤ)) (E t : ℤ)).filter
          (fun i => 0 < k i ∧ k i ≤ ((t : ℝ) : EReal))).card : ℕ) : ℝ) := by
  set T := Finset.Ioc (-(c : ℤ)) (E t : ℤ) with hT
  have hpair : ∀ (g : ℝ → ℝ) (s : ℝ≥0), s ≤ t →
      pair g (μ s) = ∑ i ∈ T, Tm H g (k i) (v i) (s : ℝ) := by
    intro g s hst
    rw [hμ, pair_sum _ _ _ (fun i _ => by
      split_ifs
      · exact integrable_atom g _
      · simp)]
    refine Finset.sum_subset (Finset.Ioc_subset_Ioc_right (by exact_mod_cast hE hst)) ?_
    intro i hiT hiS
    have hlt : (E s : ℤ) < i := by
      simp only [Finset.mem_Ioc, not_and, not_le] at hiS
      exact hiS (Finset.mem_Ioc.1 hiT).1
    rw [if_neg (fun h => not_nonneg_sub_of_lt _ _ (hD s i hlt) h.1), pair_zero]
  have hmemT : ∀ i ∈ T, -(c : ℤ) < i := fun i hi => (Finset.mem_Ioc.1 hi).1
  have hcust := fun i (hi : i ∈ T) =>
    cust hf (k i) (v i) (hA i (hmemT i hi)) (hB i (hmemT i hi)) (hC i (hmemT i hi))
      (t : ℝ) t.2
  rw [hpair f t le_rfl, hpair f 0 bot_le]
  have hint : ∫ u in Set.Icc (0 : ℝ) t, pair f' (μ u.toNNReal) =
      ∑ i ∈ T, ∫ u in Set.Icc (0 : ℝ) t, Tm H f' (k i) (v i) u := by
    rw [← integral_finset_sum _ (fun i hi => (hcust i hi).2)]
    refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
    have hut : u.toNNReal ≤ t := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1]; exact hu.2
    rw [hpair f' u.toNNReal hut, Real.coe_toNNReal _ hu.1]
  rw [hint, Finset.sum_filter, Finset.natCast_card_filter, Finset.mul_sum]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl fun i hi => (hcust i hi).1]
  simp only [NNReal.coe_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib]

end F


/-! ### G. Residual-time customers -/

lemma resid_cust (g : ℝ → ℝ≥0) (hg : Measurable g) (hfin : ∫⁻ x, (g x : ℝ≥0∞) ≤ 1)
    (hneg : ∀ x, x < 0 → g x = 0) (y : ℝ≥0) (u : ℝ) (hyH : (y : ℝ≥0∞) < edge g)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    (((QueueSeq.resid g y u : ℝ≥0∞) : EReal) + ((y : ℝ) : EReal) = ⊤ ∨
      ∃ V : ℝ, ((QueueSeq.resid g y u : ℝ≥0∞) : EReal) + ((y : ℝ) : EReal) = V ∧ 0 ≤ V ∧
        ENNReal.ofReal V < edge g) ∧
    ((y : ℝ) : EReal) < ((QueueSeq.resid g y u : ℝ≥0∞) : EReal) + ((y : ℝ) : EReal) := by
  have hyH' : ENNReal.ofReal (y : ℝ) < edge g := by rwa [ENNReal.ofReal_coe_nnreal]
  have hpos := resid_pos g hg hfin hneg (y : ℝ) u hu.1
  rcases resid_lt g hg hfin hneg (y : ℝ) u y.2 hyH' hu.2 with htop | hlt
  · rw [htop, EReal.coe_ennreal_top, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
    exact ⟨Or.inl rfl, EReal.coe_lt_top _⟩
  · by_cases htop : QueueSeq.resid g y u = ⊤
    · rw [htop, EReal.coe_ennreal_top, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      exact ⟨Or.inl rfl, EReal.coe_lt_top _⟩
    rw [← EReal.coe_ennreal_toReal htop, ← EReal.coe_add]
    have hr0 : 0 < (QueueSeq.resid g y u).toReal := ENNReal.toReal_pos hpos.ne' htop
    refine ⟨Or.inr ⟨_, rfl, by positivity, hlt⟩, ?_⟩
    exact EReal.coe_lt_coe_iff.2 (by linarith)

end PuhaWardFluid.Limit.L1aux

open PuhaWardFluid.Limit PuhaWardFluid.Limit.L1aux

theorem solution {J : ℕ} (L : ClassLaws J) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Q : QueueSeq J Ω) (N : ℕ+) (hQ : Q.IsHLPolicy L P N) :
    ∀ᵐ ω ∂P, ∀ j : Fin J,
      (∀ f f' : ℝ → ℝ, IsC1c (L.Hs j) f f' → ∀ t : ℝ≥0,
        pair f (Q.nu L N ω t j) =
          pair f (Q.nu L N ω 0 j) + (∫ u in Set.Icc (0 : ℝ) t, pair f' (Q.nu L N ω u.toNNReal j))
            - Q.Dmark L N ω (fun x _ => f x) t j + f 0 * (Q.K N ω t j : ℝ)) ∧
      (∀ ς ς' : ℝ → ℝ, IsC1c (L.Hr j) ς ς' → ∀ t : ℝ≥0,
        pair ς (Q.eta L N ω t j) =
          pair ς (Q.eta L N ω 0 j) + (∫ u in Set.Icc (0 : ℝ) t, pair ς' (Q.eta L N ω u.toNNReal j))
            - Q.Smark L N ω (fun x _ => ς x) t j + ς 0 * (Q.E N ω t j : ℝ)) := by
  classical
  obtain ⟨hPrim, -, hHL⟩ := hQ
  obtain ⟨hE1, -, -, -, -, hvlaw, hrlaw, hVu, hRu, heps, -⟩ := hPrim
  have hPprob : IsProbabilityMeasure P := by
    obtain ⟨hm, hmap⟩ := heps.2 1 one_pos
    constructor
    have := congrArg (fun μ => μ Set.univ) hmap
    simp only [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ] at this
    rw [this, unif01, Measure.restrict_apply_univ, Real.volume_Ioo]
    simp
  have hv_ae : ∀ᵐ ω ∂P, ∀ j (i : ℤ), 0 ≤ Q.v j i ω ∧ ENNReal.ofReal (Q.v j i ω) < L.Hs j := by
    rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro i
    exact ae_real_law P (L.gs j) (L.gs_meas j) (le_of_eq (L.gs_total j)) (L.gs_neg j) _
      ((hvlaw j).1 i) (fun x hx => (hvlaw j).2.2 i x hx)
  have hr_ae : ∀ᵐ ω ∂P, ∀ j (i : ℤ), 0 < i →
      Q.r j i ω = ⊤ ∨ ENNReal.ofReal (Q.r j i ω).toReal < L.Hr j := by
    rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro i
    by_cases hi : 0 < i
    · filter_upwards [ae_ennreal_law P (L.gr j) (L.gr_meas j) (L.gr_total j) (L.gr_neg j) _
        ((hrlaw j).1 i) ((hrlaw j).2.2 i hi)] with ω h _ using h
    · exact Eventually.of_forall fun ω h => absurd h hi
  have hV_ae : ∀ᵐ ω ∂P, ∀ j (i : ℤ), i ≤ 0 → Q.Vu N j i ω ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro i
    by_cases hi : i ≤ 0
    · filter_upwards [ae_unif P _ ((hVu j).2 i hi).1 ((hVu j).2 i hi).2] with ω h _ using h
    · exact Eventually.of_forall fun ω h => absurd h hi
  have hR_ae : ∀ᵐ ω ∂P, ∀ j (i : ℤ), i ≤ 0 → Q.Ru N j i ω ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro i
    by_cases hi : i ≤ 0
    · filter_upwards [ae_unif P _ ((hRu j).2 i hi).1 ((hRu j).2 i hi).2] with ω h _ using h
    · exact Eventually.of_forall fun ω h => absurd h hi
  filter_upwards [hE1, hHL, hv_ae, hr_ae, hV_ae, hR_ae] with ω hEω hHLω hvω hrω hVω hRω
  intro j
  obtain ⟨hEmono, hEcad, hE0⟩ := hEω j
  obtain ⟨-, -, hW, hAge, hkpos, hk9, -⟩ := hHLω
  -- arrivals
  have hcoe : ∀ s : ℝ≥0, ((s : ℝ) : EReal) = ((s : ℝ≥0∞) : EReal) := fun s =>
    (EReal.coe_nnreal_eq_coe_real s).symm
  have harr_le : ∀ (i : ℤ), 0 < i → ∀ s : ℝ≥0, Q.arr N ω j i ≤ ((s : ℝ) : EReal) →
      i ≤ (Q.E N ω s j : ℤ) := by
    intro i hi s h
    unfold QueueSeq.arr at h
    rw [if_neg (not_le.2 hi), hcoe, EReal.coe_ennreal_le_coe_ennreal_iff] at h
    have := (inf_le_iff (fun t => Q.E N ω t j) hEmono hEcad i.toNat s).1 h
    omega
  have harr_pos : ∀ (i : ℤ), 0 < i → (0 : EReal) < Q.arr N ω j i := by
    intro i hi
    by_contra h
    push_neg at h
    have := harr_le i hi 0 (by simpa using h)
    rw [hE0] at this
    omega
  have harr_le_t : ∀ (i : ℤ), 0 < i → ∀ s : ℝ≥0, i ≤ (Q.E N ω s j : ℤ) →
      Q.arr N ω j i ≤ ((s : ℝ) : EReal) := by
    intro i hi s h
    unfold QueueSeq.arr
    rw [if_neg (not_le.2 hi), hcoe, EReal.coe_ennreal_le_coe_ennreal_iff]
    exact iInf₂_le s (by omega)
  have hDarr : ∀ (s : ℝ≥0) (i : ℤ), (Q.E N ω s j : ℤ) < i →
      ((s : ℝ) : EReal) < Q.arr N ω j i := by
    intro s i h
    by_contra h'
    push_neg at h'
    have := harr_le i (by omega) s h'
    omega
  refine ⟨fun f f' hf t => ?_, fun ς ς' hς t => ?_⟩
  · -- service
    have hA : ∀ i, -(Q.x0 N ω j : ℤ) < i → Q.entry N ω j i ≠ ⊥ := by
      intro i _
      unfold QueueSeq.entry
      split_ifs
      · rw [← EReal.coe_neg]; exact EReal.coe_ne_bot _
      · exact EReal.coe_ennreal_ne_bot _
    have hBC : ∀ i, -(Q.x0 N ω j : ℤ) < i →
        (Q.serv L N ω j i = ⊤ ∨ ∃ V : ℝ, Q.serv L N ω j i = V ∧ 0 ≤ V ∧
          ENNReal.ofReal V < L.Hs j) ∧
        (Q.entry N ω j i ≤ 0 → -Q.entry N ω j i < Q.serv L N ω j i ∧
          ENNReal.ofReal (-(Q.entry N ω j i).toReal) < L.Hs j) := by
      intro i hi
      unfold QueueSeq.serv QueueSeq.entry
      split_ifs with hiq
      · have ha := (hAge j i hi hiq).1
        have hq0 : (0 : ℤ) ≤ (Q.q0 N ω j : ℤ) := by positivity
        have hu := hVω j i (by omega)
        obtain ⟨h1, h2⟩ := resid_cust (L.gs j) (L.gs_meas j) (le_of_eq (L.gs_total j))
          (L.gs_neg j) (Q.a0 N ω j i) _ ha hu
        refine ⟨h1, fun _ => ⟨by rwa [neg_neg], ?_⟩⟩
        rw [← EReal.coe_neg, EReal.toReal_coe, neg_neg, ENNReal.ofReal_coe_nnreal]
        exact ha
      · refine ⟨Or.inr ⟨_, rfl, (hvω j i).1, (hvω j i).2⟩, fun h => ?_⟩
        exfalso
        have := hkpos j i (by omega)
        exact absurd h (not_le.2 (EReal.coe_ennreal_pos.2 this))
    have hD : ∀ (s : ℝ≥0) (i : ℤ), (Q.E N ω s j : ℤ) < i →
        ((s : ℝ) : EReal) < Q.entry N ω j i := by
      intro s i h
      have hi0 : 0 < i := by omega
      have hiq : ¬ i ≤ -(Q.q0 N ω j : ℤ) := by omega
      by_cases htop : Q.entry N ω j i = ⊤
      · rw [htop]; exact EReal.coe_lt_top _
      · have := (hk9 j i (by omega) (lt_top_iff_ne_top.2 htop)).1
        exact lt_of_lt_of_le (hDarr s i h) this
    have key := generic1 hf (Q.x0 N ω j) (fun s => Q.E N ω s j) hEmono (Q.entry N ω j)
      (Q.serv L N ω j) (fun s => Q.nu L N ω s j) (fun s => rfl) hA
      (fun i hi => (hBC i hi).1) (fun i hi => (hBC i hi).2) hD t
    have hK : (Q.K N ω t j : ℝ) = ((((Finset.Ioc (-(Q.x0 N ω j : ℤ)) (Q.E N ω t j : ℤ)).filter
        (fun i => 0 < Q.entry N ω j i ∧ Q.entry N ω j i ≤ ((t : ℝ) : EReal))).card : ℕ) : ℝ) := by
      unfold QueueSeq.K
      congr 2
      ext i
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      have hqx : Q.q0 N ω j ≤ Q.x0 N ω j := Nat.sub_le _ _
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨by omega, h2⟩, ?_, h3⟩
        unfold QueueSeq.entry
        rw [if_neg (by omega)]
        exact EReal.coe_ennreal_pos.2 (hkpos j i h1)
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        refine ⟨⟨?_, h2⟩, h4⟩
        by_contra hle
        push_neg at hle
        unfold QueueSeq.entry at h3
        rw [if_pos hle, ← EReal.coe_neg] at h3
        have := EReal.coe_pos.1 h3
        have : (0 : ℝ) ≤ (Q.a0 N ω j i : ℝ) := (Q.a0 N ω j i).2
        linarith
    rw [hK]
    exact key
  · -- patience
    have hA : ∀ i, -(Q.m0 N ω j : ℤ) < i → Q.arr N ω j i ≠ ⊥ := by
      intro i _
      unfold QueueSeq.arr
      split_ifs
      · rw [← EReal.coe_neg]; exact EReal.coe_ne_bot _
      · exact EReal.coe_ennreal_ne_bot _
    have hBC : ∀ i, -(Q.m0 N ω j : ℤ) < i →
        (Q.pat L N ω j i = ⊤ ∨ ∃ V : ℝ, Q.pat L N ω j i = V ∧ 0 ≤ V ∧
          ENNReal.ofReal V < L.Hr j) ∧
        (Q.arr N ω j i ≤ 0 → -Q.arr N ω j i < Q.pat L N ω j i ∧
          ENNReal.ofReal (-(Q.arr N ω j i).toReal) < L.Hr j) := by
      intro i hi
      by_cases hi0 : i ≤ 0
      · have hw := (hW j i hi hi0).1
        have hu := hRω j i hi0
        obtain ⟨h1, h2⟩ := resid_cust (L.gr j) (L.gr_meas j) (L.gr_total j)
          (L.gr_neg j) (Q.w0 N ω j i) _ hw hu
        unfold QueueSeq.pat QueueSeq.arr
        rw [if_pos hi0, if_pos hi0]
        refine ⟨h1, fun _ => ⟨by rwa [neg_neg], ?_⟩⟩
        rw [← EReal.coe_neg, EReal.toReal_coe, neg_neg, ENNReal.ofReal_coe_nnreal]
        exact hw
      · have hi' : 0 < i := by omega
        refine ⟨?_, fun h => absurd h (not_le.2 (harr_pos i hi'))⟩
        unfold QueueSeq.pat
        rw [if_neg hi0]
        by_cases htop : Q.r j i ω = ⊤
        · left; rw [htop]; rfl
        · right
          have hlt := (hrω j i hi').resolve_left htop
          refine ⟨_, ?_, ENNReal.toReal_nonneg, hlt⟩
          rw [EReal.coe_ennreal_toReal htop]
    have key := generic1 hς (Q.m0 N ω j) (fun s => Q.E N ω s j) hEmono (Q.arr N ω j)
      (Q.pat L N ω j) (fun s => Q.eta L N ω s j) (fun s => rfl) hA
      (fun i hi => (hBC i hi).1) (fun i hi => (hBC i hi).2) hDarr t
    have hEt : (Q.E N ω t j : ℝ) = ((((Finset.Ioc (-(Q.m0 N ω j : ℤ)) (Q.E N ω t j : ℤ)).filter
        (fun i => 0 < Q.arr N ω j i ∧ Q.arr N ω j i ≤ ((t : ℝ) : EReal))).card : ℕ) : ℝ) := by
      have hset : (Finset.Ioc (-(Q.m0 N ω j : ℤ)) (Q.E N ω t j : ℤ)).filter
          (fun i => 0 < Q.arr N ω j i ∧ Q.arr N ω j i ≤ ((t : ℝ) : EReal)) =
          Finset.Ioc 0 (Q.E N ω t j : ℤ) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩
          refine ⟨?_, h2⟩
          by_contra hle
          push_neg at hle
          unfold QueueSeq.arr at h3
          rw [if_pos hle, ← EReal.coe_neg] at h3
          have := EReal.coe_pos.1 h3
          have : (0 : ℝ) ≤ (Q.w0 N ω j i : ℝ) := (Q.w0 N ω j i).2
          linarith
        · rintro ⟨h1, h2⟩
          exact ⟨⟨by omega, h2⟩, harr_pos i h1, harr_le_t i h1 t h2⟩
      rw [hset, Int.card_Ioc]
      simp
    rw [hEt]
    exact key
