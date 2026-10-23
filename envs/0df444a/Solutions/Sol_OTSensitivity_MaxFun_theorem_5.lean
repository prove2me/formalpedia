-- Prove2me | solution 1 for OTSensitivity.MaxFun.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-22T20:22:16.524428+00:00
-- url     : https://prove2.me/submissions/661cf1fb-5788-4b0c-aa3f-448908d527c7

import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting

open MeasureTheory ProbabilityTheory Topology Set
open scoped ENNReal

namespace OTSensitivity.MaxFun.Aux5

variable {𝒴 : Type*} [MeasurableSpace 𝒴]

/-- The swap lemma: the product coupling is strictly improvable. -/
theorem swap_lt (k : 𝒴 → 𝒴 → ℝ≥0∞) (ν ρ : Measure 𝒴) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] (U1 U2 : Set 𝒴) (hU1 : MeasurableSet U1) (hU2 : MeasurableSet U2)
    (hdis : Disjoint U1 U2) (L η : ℝ≥0∞)
    (hL : ∀ a ∈ U1, ∀ b ∈ U2, L ≤ k a b) (hη1 : ∀ a ∈ U1, ∀ b ∈ U1, k a b ≤ η)
    (hη2 : ∀ a ∈ U2, ∀ b ∈ U2, k a b ≤ η) (hηL : 2 * η < L)
    (ha : ν U1 ≠ 0) (hb : ν U2 ≠ 0) (hc : ρ U1 ≠ 0) (hd : ρ U2 ≠ 0)
    (hfin : ∫⁻ w, k w.1 w.2 ∂(ν.prod ρ) ≠ ⊤) :
    RWPI.SqrtLasso.transportCost k ν ρ < ∫⁻ w, k w.1 w.2 ∂(ν.prod ρ) := by
  set a := ν U1 with ha_def
  set b := ν U2 with hb_def
  set c := ρ U1 with hc_def
  set d := ρ U2 with hd_def
  set α := ν.restrict U1
  set β := ν.restrict U2
  set γ := ρ.restrict U1
  set δ := ρ.restrict U2
  set S := U1 ×ˢ U2 ∪ U2 ×ˢ U1 with hS
  set R := (ν.prod ρ).restrict Sᶜ with hR
  have hS_meas : MeasurableSet S := (hU1.prod hU2).union (hU2.prod hU1)
  have hdis' : Disjoint (U1 ×ˢ U2) (U2 ×ˢ U1) := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨hx, _⟩ ⟨hx', _⟩
    exact Set.disjoint_left.1 hdis hx hx'
  have hPi : ν.prod ρ = R + α.prod δ + β.prod γ := by
    rw [Measure.prod_restrict, Measure.prod_restrict, add_assoc,
      ← Measure.restrict_union hdis' (hU2.prod hU1), hR, add_comm,
      Measure.restrict_add_restrict_compl hS_meas]
  have ha1 : a ≤ 1 := prob_le_one
  have hb1 : b ≤ 1 := prob_le_one
  have hc1 : c ≤ 1 := prob_le_one
  have hd1 : d ≤ 1 := prob_le_one
  have hbc : b * c ≤ 1 := mul_le_one' hb1 hc1
  have had : a * d ≤ 1 := mul_le_one' ha1 hd1
  set π' : Measure (𝒴 × 𝒴) := R + (1 - b * c) • α.prod δ + (1 - a * d) • β.prod γ
    + (b * d) • α.prod γ + (a * c) • β.prod δ with hπ'
  have hαu : α univ = a := by simp [α, a]
  have hβu : β univ = b := by simp [β, b]
  have hγu : γ univ = c := by simp [γ, c]
  have hδu : δ univ = d := by simp [δ, d]
  have e1 : (1 - b * c) + b * c = 1 := tsub_add_cancel_of_le hbc
  have e2 : (1 - a * d) + a * d = 1 := tsub_add_cancel_of_le had
  have hfst : π'.map Prod.fst = ν := by
    have hν : ν = R.map Prod.fst + d • α + c • β := by
      have := congrArg (Measure.map Prod.fst) hPi
      rw [Measure.map_fst_prod, measure_univ, one_smul] at this
      rw [this, Measure.map_add _ _ measurable_fst, Measure.map_add _ _ measurable_fst,
        Measure.map_fst_prod, Measure.map_fst_prod, hδu, hγu]
    rw [hπ', Measure.map_add _ _ measurable_fst, Measure.map_add _ _ measurable_fst,
      Measure.map_add _ _ measurable_fst, Measure.map_add _ _ measurable_fst,
      Measure.map_smul, Measure.map_smul, Measure.map_smul, Measure.map_smul,
      Measure.map_fst_prod, Measure.map_fst_prod, Measure.map_fst_prod, Measure.map_fst_prod,
      hδu, hγu]
    conv_rhs => rw [hν]
    ext s hs
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [show R.map Prod.fst s + d * α s + c * β s
        = R.map Prod.fst s + ((1 - b * c) + b * c) * (d * α s)
          + ((1 - a * d) + a * d) * (c * β s) by rw [e1, e2, one_mul, one_mul]]
    ring
  have hsnd : π'.map Prod.snd = ρ := by
    have hρ : ρ = R.map Prod.snd + a • δ + b • γ := by
      have := congrArg (Measure.map Prod.snd) hPi
      rw [Measure.map_snd_prod, measure_univ, one_smul] at this
      rw [this, Measure.map_add _ _ measurable_snd, Measure.map_add _ _ measurable_snd,
        Measure.map_snd_prod, Measure.map_snd_prod, hαu, hβu]
    rw [hπ', Measure.map_add _ _ measurable_snd, Measure.map_add _ _ measurable_snd,
      Measure.map_add _ _ measurable_snd, Measure.map_add _ _ measurable_snd,
      Measure.map_smul, Measure.map_smul, Measure.map_smul, Measure.map_smul,
      Measure.map_snd_prod, Measure.map_snd_prod, Measure.map_snd_prod, Measure.map_snd_prod,
      hαu, hβu]
    conv_rhs => rw [hρ]
    ext s hs
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [show R.map Prod.snd s + a * δ s + b * γ s
        = R.map Prod.snd s + ((1 - b * c) + b * c) * (a * δ s)
          + ((1 - a * d) + a * d) * (b * γ s) by rw [e1, e2, one_mul, one_mul]]
    ring
  have hprob : IsProbabilityMeasure π' := by
    constructor
    have := congrArg (fun m : Measure 𝒴 => m univ) hfst
    simp only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ,
      measure_univ] at this
    exact this
  have hT : RWPI.SqrtLasso.transportCost k ν ρ ≤ ∫⁻ w, k w.1 w.2 ∂π' :=
    iInf₂_le π' ⟨hprob, hfst, hsnd⟩
  -- cost bookkeeping
  set r := ∫⁻ w, k w.1 w.2 ∂(R)
  set P1 := ∫⁻ w, k w.1 w.2 ∂(α.prod δ)
  set P2 := ∫⁻ w, k w.1 w.2 ∂(β.prod γ)
  set Q1 := ∫⁻ w, k w.1 w.2 ∂(α.prod γ)
  set Q2 := ∫⁻ w, k w.1 w.2 ∂(β.prod δ)
  have hcost : ∫⁻ w, k w.1 w.2 ∂(ν.prod ρ) = r + P1 + P2 := by
    conv_lhs => rw [hPi]
    rw [lintegral_add_measure, lintegral_add_measure]
  have hcost' : ∫⁻ w, k w.1 w.2 ∂π' = r + (1 - b * c) * P1 + (1 - a * d) * P2
      + (b * d) * Q1 + (a * c) * Q2 := by
    rw [hπ']
    simp only [lintegral_add_measure, lintegral_smul_measure, smul_eq_mul]
    rfl
  have hQ1 : Q1 ≤ η * (a * c) := by
    have h1 : α.prod γ = (ν.prod ρ).restrict (U1 ×ˢ U1) := Measure.prod_restrict _ _
    calc Q1 ≤ ∫⁻ _, η ∂(α.prod γ) := by
          apply lintegral_mono_ae
          rw [h1]
          filter_upwards [ae_restrict_mem (hU1.prod hU1)] with w hw
          exact hη1 _ hw.1 _ hw.2
      _ = η * (a * c) := by
          rw [lintegral_const, ← Set.univ_prod_univ, Measure.prod_prod, hαu, hγu]
  have hQ2 : Q2 ≤ η * (b * d) := by
    have h1 : β.prod δ = (ν.prod ρ).restrict (U2 ×ˢ U2) := Measure.prod_restrict _ _
    calc Q2 ≤ ∫⁻ _, η ∂(β.prod δ) := by
          apply lintegral_mono_ae
          rw [h1]
          filter_upwards [ae_restrict_mem (hU2.prod hU2)] with w hw
          exact hη2 _ hw.1 _ hw.2
      _ = η * (b * d) := by
          rw [lintegral_const, ← Set.univ_prod_univ, Measure.prod_prod, hβu, hδu]
  have hP1 : L * (a * d) ≤ P1 := by
    have h1 : α.prod δ = (ν.prod ρ).restrict (U1 ×ˢ U2) := Measure.prod_restrict _ _
    calc L * (a * d) = ∫⁻ _, L ∂(α.prod δ) := by
          rw [lintegral_const, ← Set.univ_prod_univ, Measure.prod_prod, hαu, hδu]
      _ ≤ P1 := by
          apply lintegral_mono_ae
          rw [h1]
          filter_upwards [ae_restrict_mem (hU1.prod hU2)] with w hw
          exact hL _ hw.1 _ hw.2
  have hP1fin : P1 ≠ ⊤ := by
    intro h; apply hfin; rw [hcost, h]; simp
  set Z := a * b * c * d with hZ
  have hZ0 : Z ≠ 0 := by simp [hZ, ha, hb, hc, hd]
  have hZtop : Z ≠ ⊤ := by
    apply ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ?_) ?_ <;>
      exact ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
  have hkey : (b * d) * (η * (a * c)) + (a * c) * (η * (b * d)) < (b * c) * P1 := by
    calc (b * d) * (η * (a * c)) + (a * c) * (η * (b * d)) = (2 * η) * Z := by
          rw [hZ]; ring
      _ < L * Z := ENNReal.mul_lt_mul_left hZ0 hZtop hηL
      _ = (b * c) * (L * (a * d)) := by rw [hZ]; ring
      _ ≤ (b * c) * P1 := by gcongr
  have hpre : r + (1 - b * c) * P1 + P2 ≠ ⊤ := by
    have : r + (1 - b * c) * P1 + P2 ≤ r + P1 + P2 := by
      gcongr
      calc (1 - b * c) * P1 ≤ 1 * P1 := by gcongr; exact tsub_le_self
        _ = P1 := one_mul _
    exact ne_top_of_le_ne_top (hcost ▸ hfin) this
  calc RWPI.SqrtLasso.transportCost k ν ρ ≤ ∫⁻ w, k w.1 w.2 ∂π' := hT
    _ = r + (1 - b * c) * P1 + (1 - a * d) * P2 + (b * d) * Q1 + (a * c) * Q2 := hcost'
    _ ≤ r + (1 - b * c) * P1 + P2 + ((b * d) * (η * (a * c)) + (a * c) * (η * (b * d))) := by
        rw [add_assoc _ ((b * d) * Q1)]
        gcongr
        calc (1 - a * d) * P2 ≤ 1 * P2 := by gcongr; exact tsub_le_self
          _ = P2 := one_mul _
    _ < r + (1 - b * c) * P1 + P2 + (b * c) * P1 := ENNReal.add_lt_add_left hpre hkey
    _ = r + ((1 - b * c) + b * c) * P1 + P2 := by ring
    _ = ∫⁻ w, k w.1 w.2 ∂(ν.prod ρ) := by rw [e1, one_mul, hcost]


section Topo
variable {𝒴 : Type*} [TopologicalSpace 𝒴] [MeasurableSpace 𝒴]

theorem exists_sets [T2Space 𝒴] (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k) {y1 y2 : 𝒴}
    (hne : y1 ≠ y2) :
    ∃ U1 U2 : Set 𝒴, IsOpen U1 ∧ IsOpen U2 ∧ y1 ∈ U1 ∧ y2 ∈ U2 ∧ Disjoint U1 U2 ∧
      ∃ L η : ℝ≥0∞, (∀ a ∈ U1, ∀ b ∈ U2, L ≤ k a b) ∧ (∀ a ∈ U1, ∀ b ∈ U1, k a b ≤ η) ∧
        (∀ a ∈ U2, ∀ b ∈ U2, k a b ≤ η) ∧ 2 * η < L := by
  have hk12 : 0 < k y1 y2 := pos_iff_ne_zero.2 (fun h => hne ((hk.2 y1 y2).1 h))
  obtain ⟨L, hL0, hL⟩ := exists_between hk12
  have hLtop : L ≠ ⊤ := ne_top_of_lt hL
  set η := L / 2 / 2 with hη
  have hη0 : 0 < η := ENNReal.half_pos (ENNReal.half_pos hL0.ne').ne'
  have h2η : 2 * η < L := by
    rw [hη, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
    exact ENNReal.half_lt_self hL0.ne' hLtop
  have hc := hk.1
  have o1 : IsOpen {p : 𝒴 × 𝒴 | L < Function.uncurry k p} := isOpen_lt continuous_const hc
  have o2 : IsOpen {p : 𝒴 × 𝒴 | Function.uncurry k p < η} := isOpen_lt hc continuous_const
  obtain ⟨u, v, hu, hv, hy1u, hy2v, huv⟩ := isOpen_prod_iff.1 o1 y1 y2 hL
  have hd1 : k y1 y1 < η := by rw [(hk.2 y1 y1).2 rfl]; exact hη0
  have hd2 : k y2 y2 < η := by rw [(hk.2 y2 y2).2 rfl]; exact hη0
  obtain ⟨u1, v1, hu1, hv1, hy1u1, hy1v1, h11⟩ := isOpen_prod_iff.1 o2 y1 y1 hd1
  obtain ⟨u2, v2, hu2, hv2, hy2u2, hy2v2, h22⟩ := isOpen_prod_iff.1 o2 y2 y2 hd2
  obtain ⟨s, t, hs, ht, hy1s, hy2t, hst⟩ := t2_separation hne
  refine ⟨s ∩ u ∩ u1 ∩ v1, t ∩ v ∩ u2 ∩ v2, ((hs.inter hu).inter hu1).inter hv1,
    ((ht.inter hv).inter hu2).inter hv2, ⟨⟨⟨hy1s, hy1u⟩, hy1u1⟩, hy1v1⟩,
    ⟨⟨⟨hy2t, hy2v⟩, hy2u2⟩, hy2v2⟩, ?_, L, η, ?_, ?_, ?_, h2η⟩
  · exact hst.mono (fun x hx => hx.1.1.1) (fun x hx => hx.1.1.1)
  · intro a ha b hb
    exact le_of_lt (huv (Set.mk_mem_prod ha.1.1.2 hb.1.1.2))
  · intro a ha b hb
    exact le_of_lt (h11 (Set.mk_mem_prod ha.1.2 hb.2))
  · intro a ha b hb
    exact le_of_lt (h22 (Set.mk_mem_prod ha.1.2 hb.2))

theorem dirac_of_eq [SecondCountableTopology 𝒴] [T2Space 𝒴] [OpensMeasurableSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k) (ν ρ : Measure 𝒴) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ]
    (hsupp : ∀ U, IsOpen U → ν U = 0 → ρ U = 0)
    (hfin : ∫⁻ w, k w.1 w.2 ∂(ν.prod ρ) ≠ ⊤)
    (heq : ∫⁻ w, k w.1 w.2 ∂(ν.prod ρ) ≤ RWPI.SqrtLasso.transportCost k ν ρ) :
    ∃ z, ρ {z}ᶜ = 0 := by
  by_contra hnd
  push_neg at hnd
  set S := {y : 𝒴 | ∀ U, IsOpen U → y ∈ U → ρ U ≠ 0} with hSdef
  have hSc : ρ Sᶜ = 0 := by
    apply measure_null_of_locally_null
    intro x hx
    simp only [hSdef, mem_compl_iff, mem_setOf_eq, not_forall, not_not] at hx
    obtain ⟨U, hU, hxU, hρU⟩ := hx
    exact ⟨U, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU), hρU⟩
  obtain ⟨y1, hy1⟩ : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, compl_empty, measure_univ] at hSc
    exact one_ne_zero hSc
  obtain ⟨y2, hy2, hne⟩ : ∃ y2 ∈ S, y2 ≠ y1 := by
    by_contra h
    push_neg at h
    apply hnd y1
    apply measure_mono_null _ hSc
    intro y hy hyS
    exact hy (h y hyS)
  obtain ⟨U1, U2, hU1, hU2, hy1U, hy2U, hdis, L, η, hL, hη1, hη2, hηL⟩ :=
    exists_sets k hk hne.symm
  have pos : ∀ y ∈ S, ∀ U, IsOpen U → y ∈ U → ν U ≠ 0 ∧ ρ U ≠ 0 := fun y hy U hU hyU =>
    ⟨fun h => hy U hU hyU (hsupp U hU h), hy U hU hyU⟩
  have := swap_lt k ν ρ U1 U2 hU1.measurableSet hU2.measurableSet hdis L η hL hη1 hη2 hηL
    (pos y1 hy1 U1 hU1 hy1U).1 (pos y2 hy2 U2 hU2 hy2U).1 (pos y1 hy1 U1 hU1 hy1U).2
    (pos y2 hy2 U2 hU2 hy2U).2 hfin
  exact absurd heq (not_le.2 this)

end Topo

theorem lower_dirac {𝒴 : Type*} [MeasurableSpace 𝒴] [MeasurableSingletonClass 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hkm : ∀ z, Measurable fun y => k y z) (ν ρ : Measure 𝒴) (z : 𝒴)
    (hρ : ρ {z}ᶜ = 0) :
    ∫⁻ y, k y z ∂ν ≤ RWPI.SqrtLasso.transportCost k ν ρ := by
  unfold RWPI.SqrtLasso.transportCost
  refine le_iInf₂ fun π hπ => ?_
  obtain ⟨_, h1, h2⟩ := hπ
  have hae : ∀ᵐ w ∂π, w.2 = z := by
    rw [ae_iff]
    have : π.map Prod.snd {z}ᶜ = 0 := by rw [h2]; exact hρ
    rw [Measure.map_apply measurable_snd (measurableSet_singleton z).compl] at this
    exact this
  refine le_of_eq ?_
  calc ∫⁻ y, k y z ∂ν = ∫⁻ w, k w.1 z ∂π := by rw [← h1, lintegral_map (hkm z) measurable_fst]
    _ = ∫⁻ w, k w.1 w.2 ∂π := lintegral_congr_ae (by filter_upwards [hae] with w hw; rw [hw])

theorem tc_le_prod {𝒴 : Type*} [MeasurableSpace 𝒴] (k : 𝒴 → 𝒴 → ℝ≥0∞) (ν ρ : Measure 𝒴)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    RWPI.SqrtLasso.transportCost k ν ρ ≤ ∫⁻ w, k w.1 w.2 ∂(ν.prod ρ) :=
  iInf₂_le (ν.prod ρ) ⟨inferInstance, by simp, by simp⟩

section Disint
variable {Ω 𝒳 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]

theorem meas_lint (κ : 𝒳 → Measure 𝒴) (hκB : ∀ B, MeasurableSet B → Measurable fun x => κ x B)
    {g : 𝒴 → ℝ≥0∞} (hg : Measurable g) : Measurable fun x => ∫⁻ y, g y ∂κ x :=
  (Measure.measurable_lintegral hg).comp (Measure.measurable_of_measurable_coe κ hκB)

theorem inner_eq [MeasurableSingletonClass 𝒴] (ρ : Measure 𝒴) (f : 𝒳 → 𝒴) (x : 𝒳) :
    ∫⁻ y, ({p : 𝒳 × 𝒴 | f p.1 = p.2}ᶜ).indicator (1 : 𝒳 × 𝒴 → ℝ≥0∞) (x, y) ∂ρ = ρ {f x}ᶜ := by
  have : (fun y => ({p : 𝒳 × 𝒴 | f p.1 = p.2}ᶜ).indicator (1 : 𝒳 × 𝒴 → ℝ≥0∞) (x, y))
      = ({f x}ᶜ : Set 𝒴).indicator 1 := by
    ext y
    by_cases h : y = f x
    · subst h; simp
    · simp [Set.indicator_apply, h, Ne.symm h]
  rw [this, lintegral_indicator_one (measurableSet_singleton _).compl]

theorem meas_E [MeasurableEq 𝒴] [MeasurableSingletonClass 𝒴] (κ : 𝒳 → Measure 𝒴)
    (hκB : ∀ B, MeasurableSet B → Measurable fun x => κ x B)
    (hprob : ∀ x, IsProbabilityMeasure (κ x)) (f : 𝒳 → 𝒴) (hf : Measurable f) :
    Measurable fun x => κ x {f x}ᶜ := by
  let K : Kernel 𝒳 𝒴 := ⟨κ, Measure.measurable_of_measurable_coe κ hκB⟩
  have : IsMarkovKernel K := ⟨hprob⟩
  have hS : MeasurableSet ({p : 𝒳 × 𝒴 | f p.1 = p.2}ᶜ) :=
    (measurableSet_eq_fun (hf.comp measurable_fst) measurable_snd).compl
  have hφ : Measurable (({p : 𝒳 × 𝒴 | f p.1 = p.2}ᶜ).indicator (1 : 𝒳 × 𝒴 → ℝ≥0∞)) :=
    measurable_one.indicator hS
  have := hφ.lintegral_kernel_prod_right' (κ := K)
  have h2 : (fun x => κ x {f x}ᶜ) = fun x => ∫⁻ y,
      ({p : 𝒳 × 𝒴 | f p.1 = p.2}ᶜ).indicator (1 : 𝒳 × 𝒴 → ℝ≥0∞) (x, y) ∂K x := by
    funext x; exact (inner_eq (κ x) f x).symm
  rw [h2]; exact this

theorem disint (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → 𝒳) (Y : Ω → 𝒴)
    (hX : Measurable X) (hY : Measurable Y)
    (κ : 𝒳 → Measure 𝒴) (hκB : ∀ B, MeasurableSet B → Measurable fun x => κ x B)
    (hprob : ∀ x, IsProbabilityMeasure (κ x))
    (hcond : ∀ A, MeasurableSet A → ∀ B, MeasurableSet B →
      P (X ⁻¹' A ∩ Y ⁻¹' B) = ∫⁻ ω in X ⁻¹' A, κ (X ω) B ∂P)
    (φ : 𝒳 × 𝒴 → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ ω, ∫⁻ y, φ (X ω, y) ∂κ (X ω) ∂P = ∫⁻ ω, φ (X ω, Y ω) ∂P := by
  let K : Kernel 𝒳 𝒴 := ⟨κ, Measure.measurable_of_measurable_coe κ hκB⟩
  haveI : IsMarkovKernel K := ⟨hprob⟩
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hXY : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have hM : (P.map X) ⊗ₘ K = P.map (fun ω => (X ω, Y ω)) := by
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      rw [Measure.compProd_apply_prod hA hB, Measure.map_apply hXY (hA.prod hB)]
      show _ = P (X ⁻¹' A ∩ Y ⁻¹' B)
      rw [hcond A hA B hB]
      exact setLIntegral_map hA (hκB B hB) hX
    · have : IsProbabilityMeasure (P.map (fun ω => (X ω, Y ω))) :=
        Measure.isProbabilityMeasure_map hXY.aemeasurable
      simp only [measure_univ]
  have hin : Measurable fun x => ∫⁻ y, φ (x, y) ∂K x := hφ.lintegral_kernel_prod_right'
  calc ∫⁻ ω, ∫⁻ y, φ (X ω, y) ∂κ (X ω) ∂P
        = ∫⁻ x, ∫⁻ y, φ (x, y) ∂K x ∂(P.map X) := (lintegral_map hin hX).symm
    _ = ∫⁻ p, φ p ∂((P.map X) ⊗ₘ K) := (Measure.lintegral_compProd hφ).symm
    _ = ∫⁻ ω, φ (X ω, Y ω) ∂P := by rw [hM, lintegral_map hφ hXY]

theorem key_E [MeasurableEq 𝒴] [MeasurableSingletonClass 𝒴] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → 𝒳) (Y : Ω → 𝒴)
    (hX : Measurable X) (hY : Measurable Y)
    (κ : 𝒳 → Measure 𝒴) (hκB : ∀ B, MeasurableSet B → Measurable fun x => κ x B)
    (hprob : ∀ x, IsProbabilityMeasure (κ x))
    (hcond : ∀ A, MeasurableSet A → ∀ B, MeasurableSet B →
      P (X ⁻¹' A ∩ Y ⁻¹' B) = ∫⁻ ω in X ⁻¹' A, κ (X ω) B ∂P)
    (f : 𝒳 → 𝒴) (hf : Measurable f) :
    (∀ᵐ ω ∂P, κ (X ω) {f (X ω)}ᶜ = 0) ↔ Y =ᵐ[P] f ∘ X := by
  set S : Set (𝒳 × 𝒴) := {p | f p.1 = p.2}ᶜ with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_eq_fun (hf.comp measurable_fst) measurable_snd).compl
  have hφ : Measurable (S.indicator (1 : 𝒳 × 𝒴 → ℝ≥0∞)) := measurable_one.indicator hS
  have hD := disint P X Y hX hY κ hκB hprob hcond _ hφ
  simp only [hSdef, inner_eq] at hD
  have hm1 : Measurable fun ω => κ (X ω) {f (X ω)}ᶜ := (meas_E κ hκB hprob f hf).comp hX
  have hm2 : Measurable fun ω => S.indicator (1 : 𝒳 × 𝒴 → ℝ≥0∞) (X ω, Y ω) :=
    hφ.comp (hX.prodMk hY)
  have hpt : ∀ ω, S.indicator (1 : 𝒳 × 𝒴 → ℝ≥0∞) (X ω, Y ω) = 0 ↔ Y ω = f (X ω) := by
    intro ω
    by_cases h : Y ω = f (X ω)
    · simp [hSdef, h]
    · simp [hSdef, h, Set.indicator_apply, Ne.symm h]
  constructor
  · intro h
    have h1 : ∫⁻ ω, κ (X ω) {f (X ω)}ᶜ ∂P = 0 := (lintegral_eq_zero_iff hm1).2 h
    rw [hD] at h1
    filter_upwards [(lintegral_eq_zero_iff hm2).1 h1] with ω hω
    exact (hpt ω).1 hω
  · intro h
    have h2 : ∫⁻ ω, S.indicator (1 : 𝒳 × 𝒴 → ℝ≥0∞) (X ω, Y ω) ∂P = 0 :=
      (lintegral_eq_zero_iff hm2).2 (by filter_upwards [h] with ω hω; exact (hpt ω).2 hω)
    rw [← hD] at h2
    exact (lintegral_eq_zero_iff hm1).1 h2

end Disint

end OTSensitivity.MaxFun.Aux5

namespace OTSensitivity.MaxFun

open Aux5

theorem theorem_5 {Ω 𝒳 𝒴 : Type*} [MeasurableSpace Ω]
    [TopologicalSpace 𝒳] [PolishSpace 𝒳] [m𝒳 : MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝒳) (Y : Ω → 𝒴) (hX : Measurable X) (hY : Measurable Y)
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (hMK : MK k (P.map Y) < ⊤)
    (F : MeasurableSpace 𝒳) (hF : F ≤ m𝒳) (κ : Kernel 𝒳 𝒴) (hκ : IsCondDistrib P X Y F κ) :
    xi k P X Y κ ≤ MK k (P.map Y) ∧
      (xi k P X Y κ = MK k (P.map Y) ↔ IsFunctionallyDependent P X Y F) := by
  obtain ⟨hmk, hκF, hcondF⟩ := hκ
  have hXF : @Measurable Ω 𝒳 _ F X := hX.mono le_rfl hF
  clear hX
  set μ := P.map X with hμ
  set ν := P.map Y with hν
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hXF.aemeasurable
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hkm : Measurable (Function.uncurry k) := hk.1.measurable
  have hkm1 : ∀ z, Measurable fun y => k y z := fun z =>
    hkm.comp (measurable_id.prodMk measurable_const)
  have hcond' : ∀ A, MeasurableSet[F] A → ∀ B : Set 𝒴, MeasurableSet B →
      P (X ⁻¹' A ∩ Y ⁻¹' B) = ∫⁻ ω in X ⁻¹' A, κ (X ω) B ∂P := by
    intro A hA B hB
    rw [hcondF A hA B hB, setLIntegral_map hA (κ.measurable_coe hB) hXF]
  have hprob : ∀ x, IsProbabilityMeasure (κ x) := fun x => inferInstance
  have hxi : xi k P X Y κ = ∫⁻ x, RWPI.SqrtLasso.transportCost k ν (κ x) ∂μ := rfl
  set g : 𝒴 → ℝ≥0∞ := fun y' => ∫⁻ y, k y y' ∂ν with hg
  have hgm : Measurable g := hkm.lintegral_prod_left'
  set G : 𝒳 → ℝ≥0∞ := fun x => ∫⁻ y', g y' ∂κ x with hG
  have hGm : Measurable G := hgm.lintegral_kernel
  have hprodG : ∀ x, ∫⁻ w, k w.1 w.2 ∂(ν.prod (κ x)) = G x := fun x =>
    lintegral_prod_symm _ hkm.aemeasurable
  have hTG : ∀ x, RWPI.SqrtLasso.transportCost k ν (κ x) ≤ G x := fun x =>
    (tc_le_prod k ν (κ x)).trans_eq (hprodG x)
  have hIntG : ∫⁻ x, G x ∂μ = MK k ν := by
    have hD := disint P X Y hXF hY (fun x => κ x) (fun B hB => κ.measurable_coe hB) hprob hcond'
      (fun p => g p.2) (hgm.comp measurable_snd)
    calc ∫⁻ x, G x ∂μ = ∫⁻ ω, G (X ω) ∂P := lintegral_map hGm hXF
      _ = ∫⁻ ω, g (Y ω) ∂P := hD
      _ = ∫⁻ y', g y' ∂ν := (lintegral_map hgm hY).symm
      _ = MK k ν := (lintegral_lintegral_swap hkm.aemeasurable).symm
  have hle : xi k P X Y κ ≤ MK k ν := by
    rw [hxi, ← hIntG]; exact lintegral_mono hTG
  refine ⟨hle, ⟨fun heq => ?_, fun hfd => ?_⟩⟩
  · -- equality forces functional dependence
    have hMK' : MK k ν ≠ ⊤ := hMK.ne
    have hae : (fun x => RWPI.SqrtLasso.transportCost k ν (κ x)) =ᵐ[μ] G :=
      ae_eq_of_ae_le_of_lintegral_le (ae_of_all _ hTG)
        (by rw [← hxi, heq]; exact hMK') hGm.aemeasurable
        (by rw [hIntG, ← hxi, heq])
    have hGfin : ∀ᵐ x ∂μ, G x < ⊤ := ae_lt_top hGm (hIntG ▸ hMK')
    set N := {y : 𝒴 | ∃ U, IsOpen U ∧ y ∈ U ∧ ν U = 0} with hNdef
    have hNopen : IsOpen N := by
      refine isOpen_iff_forall_mem_open.2 fun y hy => ?_
      obtain ⟨U, hU, hyU, h0⟩ := hy
      exact ⟨U, fun z hz => ⟨U, hU, hz, h0⟩, hU, hyU⟩
    have hN0 : ν N = 0 := by
      refine measure_null_of_locally_null N (fun y hy => ?_)
      obtain ⟨U, hU, hyU, h0⟩ := hy
      exact ⟨U, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hyU), h0⟩
    have hκN : ∀ᵐ x ∂μ, κ x N = 0 := by
      have h0 : ∫⁻ x, κ x N ∂μ = 0 := by
        have := hcondF univ MeasurableSet.univ N hNopen.measurableSet
        rw [Measure.restrict_univ, preimage_univ, univ_inter] at this
        rw [← this, ← Measure.map_apply hY hNopen.measurableSet]; exact hN0
      exact (lintegral_eq_zero_iff (κ.measurable_coe hNopen.measurableSet)).1 h0
    have hdirac : ∀ᵐ x ∂μ, ∃ z, κ x {z}ᶜ = 0 := by
      filter_upwards [hae, hGfin, hκN] with x h1 h2 h3
      apply dirac_of_eq k hk ν (κ x)
      · intro U hU hνU; exact measure_mono_null (fun y hy => show y ∈ N from ⟨U, hU, hy, hνU⟩) h3
      · rw [hprodG x]; exact h2.ne
      · rw [hprodG x]; exact h1.symm.le
    -- a measurable embedding into ℝ≥0∞
    set e := embeddingReal 𝒴
    have he := measurableEmbedding_embeddingReal 𝒴
    set ψ : 𝒴 → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (e y)) with hψ
    have hψm : Measurable ψ :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp he.measurable)
    have hψi : Function.Injective ψ := by
      intro a b h
      have := (ENNReal.ofReal_eq_ofReal_iff (Real.exp_pos _).le (Real.exp_pos _).le).1 h
      exact he.injective (Real.exp_injective this)
    have hψe : MeasurableEmbedding ψ := hψm.measurableEmbedding hψi
    haveI : (ae μ).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
    obtain ⟨x0, z0, -⟩ := hdirac.exists
    set h : 𝒳 → ℝ≥0∞ := fun x => ∫⁻ y, ψ y ∂κ x with hh
    have hhF : @Measurable 𝒳 ℝ≥0∞ F _ h := meas_lint (fun x => κ x) (fun B hB => κ.measurable_coe hB) hψm
    set f : 𝒳 → 𝒴 := fun x => Function.extend ψ id (fun _ => z0) (h x) with hf
    have hfF : @Measurable 𝒳 𝒴 F _ f :=
      (hψe.measurable_extend measurable_id measurable_const).comp hhF
    have hfa : ∀ᵐ x ∂μ, κ x {f x}ᶜ = 0 := by
      filter_upwards [hdirac] with x hx
      obtain ⟨z, hz⟩ := hx
      have hzx : h x = ψ z := by
        have hae' : ∀ᵐ y ∂κ x, y = z := by rw [ae_iff]; exact hz
        calc h x = ∫⁻ _, ψ z ∂κ x :=
              lintegral_congr_ae (by filter_upwards [hae'] with y hy; rw [hy])
          _ = ψ z := by simp
      have : f x = z := by
        simp only [hf, hzx]; exact hψi.extend_apply _ _ z
      rw [this]; exact hz
    refine ⟨f, hfF, ?_⟩
    exact (key_E P X Y hXF hY (fun x => κ x) (fun B hB => κ.measurable_coe hB) hprob hcond' f hfF).1
      (ae_of_ae_map hXF.aemeasurable hfa)
  · -- functional dependence gives equality
    obtain ⟨f, hfF, hYf⟩ := hfd
    have hfa : ∀ᵐ ω ∂P, κ (X ω) {f (X ω)}ᶜ = 0 :=
      (key_E P X Y hXF hY (fun x => κ x) (fun B hB => κ.measurable_coe hB) hprob hcond' f hfF).2 hYf
    have hfm : Measurable f := hfF
    have hm : Measurable fun x => κ x {f x}ᶜ :=
      meas_E (fun x => κ x) (fun B hB => κ.measurable_coe hB) hprob f hfm
    have hfa' : ∀ᵐ x ∂μ, κ x {f x}ᶜ = 0 := by
      rw [ae_map_iff hXF.aemeasurable (measurableSet_eq_fun hm measurable_const)]
      exact hfa
    have hlow : ∀ᵐ x ∂μ, ∫⁻ y, k y (f x) ∂ν ≤ RWPI.SqrtLasso.transportCost k ν (κ x) := by
      filter_upwards [hfa'] with x hx
      exact lower_dirac k hkm1 ν (κ x) (f x) hx
    have hpush : μ.map f = ν := by
      rw [hμ, Measure.map_map hfm hXF, hν]; exact Measure.map_congr hYf.symm
    have hge : MK k ν ≤ xi k P X Y κ := by
      calc MK k ν = ∫⁻ y, ∫⁻ y', k y y' ∂(μ.map f) ∂ν := by rw [hpush]; rfl
        _ = ∫⁻ y, ∫⁻ x, k y (f x) ∂μ ∂ν := by
            congr 1; ext y
            exact lintegral_map (hkm.comp (measurable_const.prodMk measurable_id)) hfm
        _ = ∫⁻ x, ∫⁻ y, k y (f x) ∂ν ∂μ :=
            lintegral_lintegral_swap
              ((hkm.comp (measurable_fst.prodMk (hfm.comp measurable_snd))).aemeasurable)
        _ ≤ ∫⁻ x, RWPI.SqrtLasso.transportCost k ν (κ x) ∂μ := lintegral_mono_ae hlow
        _ = xi k P X Y κ := rfl
    exact le_antisymm hle hge

end OTSensitivity.MaxFun


-- Platform entry point: restates the target verbatim.
namespace OTSensitivity.MaxFun

/-- Theorem 5, p. 10 (max-functionality): under the assumptions of Lemma 4 (`k` continuous,
vanishing exactly on the diagonal, `𝕄^K[Y] < ∞`), for every sub-σ-algebra `𝓕` of `𝓑(𝒳)` and
every version `κ` of the conditional distribution of `Y` given `(X, 𝓕)`,
`ξ^K(Y, X | 𝓕) ≤ 𝕄^K[Y]` (20), and equality holds if and only if `Y = f(X)` `P`-a.e. for some
`𝓕`-measurable `f : 𝒳 → 𝒴`. -/
theorem _root_.solution {Ω 𝒳 𝒴 : Type*} [MeasurableSpace Ω]
    [TopologicalSpace 𝒳] [PolishSpace 𝒳] [m𝒳 : MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝒳) (Y : Ω → 𝒴) (hX : Measurable X) (hY : Measurable Y)
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (hMK : MK k (P.map Y) < ⊤)
    (F : MeasurableSpace 𝒳) (hF : F ≤ m𝒳) (κ : Kernel 𝒳 𝒴) (hκ : IsCondDistrib P X Y F κ) :
    xi k P X Y κ ≤ MK k (P.map Y) ∧
      (xi k P X Y κ = MK k (P.map Y) ↔ IsFunctionallyDependent P X Y F) := by
  exact @OTSensitivity.MaxFun.theorem_5 Ω 𝒳 𝒴 _ _ _ m𝒳 _ _ _ _ _ P _ X Y hX hY k hk hMK F hF κ hκ

end OTSensitivity.MaxFun
