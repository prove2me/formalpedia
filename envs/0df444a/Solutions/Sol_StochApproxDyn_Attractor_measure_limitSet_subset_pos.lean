-- Prove2me | solution 1 for StochApproxDyn.Attractor.measure_limitSet_subset_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T13:22:46.267044+00:00
-- url     : https://prove2.me/submissions/490bddb0-858c-43d9-943f-21560546c645

import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics
import Definitions.Def_StochApproxDyn_Attractor_Process

open scoped NNReal ENNReal
open MeasureTheory

set_option autoImplicit false

namespace SAD376200c5

open StochApproxDyn.Attractor

/-- Deterministic step: a path that tracks the flow within `ε/2` over horizons `≤ 2τ` from time
`s`, starting at a point that `Φ` carries uniformly into the `ε/2`-neighbourhood of `A`, and that
is an asymptotic pseudotrajectory, has limit set inside `A`. -/
theorem det_limitSet_subset {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (A W : Set M)
    (hAne : A.Nonempty) (hAc : IsClosed A) (ε : ℝ)
    (hW : ∀ x, Metric.infDist x A < ε → x ∈ W)
    (hattr : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t → ∀ x ∈ W,
      Metric.infDist (Φ t x) A < η)
    (x : ℝ≥0 → M) (s τ : ℝ≥0) (hτ : 0 < τ)
    (h0 : ∀ t : ℝ≥0, τ ≤ t → Metric.infDist (Φ t (x s)) A < ε / 2)
    (h1 : ∀ y ∈ W, Metric.infDist (Φ τ y) A < ε / 2)
    (htr : ∀ r : ℝ≥0, s ≤ r → ∀ h : ℝ≥0, h ≤ 2 * τ → dist (x (r + h)) (Φ h (x r)) < ε / 2)
    (hapt : ∀ T : ℝ≥0, 0 < T → ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t →
      ∀ h : ℝ≥0, h ≤ T → dist (x (t + h)) (Φ h (x t)) < η) :
    StochApproxDyn.LimitSet.limitSet x ⊆ A := by
  -- Step 1: from time `s + τ` on, the path stays within `ε` of `A`.
  have step : ∀ n : ℕ, ∀ h : ℝ≥0, τ ≤ h → h ≤ ((n : ℝ≥0) + 2) * τ →
      Metric.infDist (x (s + h)) A < ε := by
    intro n
    induction n with
    | zero =>
      intro h hτh hh
      have hh' : h ≤ 2 * τ := by simpa using hh
      have e1 := htr s le_rfl h hh'
      have e2 := h0 h hτh
      calc Metric.infDist (x (s + h)) A
          ≤ Metric.infDist (Φ h (x s)) A + dist (x (s + h)) (Φ h (x s)) :=
            Metric.infDist_le_infDist_add_dist
        _ < ε / 2 + ε / 2 := add_lt_add e2 e1
        _ = ε := by ring
    | succ n ih =>
      intro h hτh hh
      by_cases hle : h ≤ ((n : ℝ≥0) + 2) * τ
      · exact ih h hτh hle
      rw [not_le, ← NNReal.coe_lt_coe] at hle
      push_cast at hle
      have hτh2 : τ ≤ h := hτh
      have hτle : τ ≤ h - τ := by
        rw [← NNReal.coe_le_coe, NNReal.coe_sub hτh2]
        nlinarith [τ.2, (Nat.cast_nonneg (α := ℝ) n)]
      have hup : h - τ ≤ ((n : ℝ≥0) + 2) * τ := by
        rw [← NNReal.coe_le_coe] at hh ⊢
        rw [NNReal.coe_sub hτh2]; push_cast at hh ⊢; nlinarith
      have hprev := ih (h - τ) hτle hup
      have hWm := hW _ hprev
      have e2 := h1 _ hWm
      have e1 := htr (s + (h - τ)) le_self_add τ (by
        rw [← NNReal.coe_le_coe]; push_cast; nlinarith [τ.2])
      have hrw : s + (h - τ) + τ = s + h := by
        rw [add_assoc, tsub_add_cancel_of_le hτh2]
      rw [hrw] at e1
      calc Metric.infDist (x (s + h)) A
          ≤ Metric.infDist (Φ τ (x (s + (h - τ)))) A
              + dist (x (s + h)) (Φ τ (x (s + (h - τ)))) :=
            Metric.infDist_le_infDist_add_dist
        _ < ε / 2 + ε / 2 := add_lt_add e2 e1
        _ = ε := by ring
  have stay : ∀ r : ℝ≥0, s + τ ≤ r → x r ∈ W := by
    intro r hr
    have hsr : s ≤ r := le_trans le_self_add hr
    obtain ⟨n, hn⟩ := exists_nat_gt ((r - s) / τ)
    apply hW
    have hh : τ ≤ r - s := by
      rw [← NNReal.coe_le_coe] at hr ⊢; rw [NNReal.coe_sub hsr]; push_cast at hr; linarith
    have hup : r - s ≤ ((n : ℝ≥0) + 2) * τ := by
      rw [div_lt_iff₀ hτ] at hn
      exact le_trans hn.le (mul_le_mul_of_nonneg_right (by simp) τ.2)
    have := step n (r - s) hh hup
    rwa [add_tsub_cancel_of_le hsr] at this
  -- Step 2: the distance to `A` tends to `0`.
  have conv : ∀ η : ℝ, 0 < η → ∃ R : ℝ≥0, ∀ r : ℝ≥0, R ≤ r → Metric.infDist (x r) A < η := by
    intro η hη
    obtain ⟨t₁, ht₁⟩ := hattr (η / 2) (by positivity)
    set T : ℝ≥0 := max t₁ 1 with hTdef
    have hT : 0 < T := lt_of_lt_of_le one_pos (le_max_right _ _)
    obtain ⟨t₀, ht₀⟩ := hapt T hT (η / 2) (by positivity)
    refine ⟨max t₀ (s + τ) + T, fun r hr => ?_⟩
    have hTr : T ≤ r := le_trans le_add_self hr
    set t := r - T with ht
    have htr' : t + T = r := tsub_add_cancel_of_le hTr
    have hmt : max t₀ (s + τ) ≤ t := by
      rw [ht]; exact le_tsub_of_add_le_right hr
    have e1 := ht₀ t (le_trans (le_max_left _ _) hmt) T le_rfl
    have e2 := ht₁ T (le_max_left _ _) (x t) (stay t (le_trans (le_max_right _ _) hmt))
    rw [htr'] at e1
    calc Metric.infDist (x r) A ≤ Metric.infDist (Φ T (x t)) A + dist (x r) (Φ T (x t)) :=
          Metric.infDist_le_infDist_add_dist
      _ < η / 2 + η / 2 := add_lt_add e2 e1
      _ = η := by ring
  -- Step 3: limit points lie in `A`.
  intro p hp
  rw [hAc.mem_iff_infDist_zero hAne]
  refine le_antisymm (le_of_forall_pos_le_add fun η hη => ?_) Metric.infDist_nonneg
  obtain ⟨R, hR⟩ := conv η hη
  have hpR : p ∈ closure (x '' Set.Ici R) := Set.mem_iInter.1 hp R
  have hcl : closure (x '' Set.Ici R) ⊆ {y | Metric.infDist y A ≤ η} := by
    apply closure_minimal
    · rintro _ ⟨r, hr, rfl⟩; exact (hR r hr).le
    · exact isClosed_le (Metric.continuous_infDist_pt A) continuous_const
  simpa using hcl hpR

/-- Off the deviation event, every deviation is below `δ`. -/
theorem dev_lt {Ω M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (t δ T : ℝ≥0) (ω : Ω) (hω : ω ∉ deviationEvent Φ X t δ T) (s : ℝ≥0) (hs : t ≤ s)
    (h : ℝ≥0) (hh : h ≤ T) : dist (X (s + h) ω) (Φ h (X s ω)) < δ := by
  simp only [deviationEvent, Set.mem_setOf_eq, not_le] at hω
  have h1 : edist (X (s + h) ω) (Φ h (X s ω)) ≤ ⨆ (s : ℝ≥0) (_ : t ≤ s) (h : ℝ≥0) (_ : h ≤ T),
      edist (X (s + h) ω) (Φ h (X s ω)) :=
    le_trans (le_iSup₂ (f := fun (h : ℝ≥0) (_ : h ≤ T) => edist (X (s + h) ω) (Φ h (X s ω))) h hh)
      (le_iSup₂ (f := fun (s : ℝ≥0) (_ : t ≤ s) =>
        ⨆ (h : ℝ≥0) (_ : h ≤ T), edist (X (s + h) ω) (Φ h (X s ω))) s hs)
  have h2 := lt_of_le_of_lt h1 hω
  have h3 : nndist (X (s + h) ω) (Φ h (X s ω)) < δ := edist_lt_coe.1 h2
  rw [dist_nndist]; exact_mod_cast h3

/-- Conditioning on an `ℱ t`-event `G`: `P(G ∩ D_t) ≤ w(t) P(G)`. -/
theorem measure_inter_dev_le {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    [MeasurableSpace M] {Φ : Flow ℝ≥0 M} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ≥0 m0} {X : ℝ≥0 → Ω → M} {w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0}
    (hX : SatisfiesStandingAssumption Φ P ℱ X w) (t δ T : ℝ≥0) (hδ : 0 < δ) (hT : 0 < T)
    (G : Set Ω) (hG : MeasurableSet[ℱ t] G) :
    P.real (G ∩ deviationEvent Φ X t δ T) ≤ (w t δ T : ℝ) * P.real G := by
  set D := deviationEvent Φ X t δ T with hDdef
  have hD : MeasurableSet D := hX.measurableSet_deviationEvent t δ T hδ hT
  have hint : Integrable (D.indicator fun _ => (1 : ℝ)) P := (integrable_const 1).indicator hD
  have e1 : ∫ ω in G, D.indicator (fun _ => (1 : ℝ)) ω ∂P = P.real (G ∩ D) := by
    rw [integral_indicator hD, setIntegral_const, measureReal_restrict_apply hD, Set.inter_comm]
    simp
  have e2 := setIntegral_condExp (ℱ.le t) hint hG
  have e3 : ∫ ω in G, (P[D.indicator (fun _ => (1 : ℝ)) | ℱ t]) ω ∂P
      ≤ ∫ ω in G, (w t δ T : ℝ) ∂P :=
    integral_mono_ae integrable_condExp.integrableOn (integrable_const _)
      (ae_restrict_of_ae (hX.condProb_le t δ T hδ hT))
  rw [setIntegral_const, e2, e1, smul_eq_mul] at e3
  linarith

/-- The events `⋂_k D_k(δ, T)` are null. -/
theorem measure_iInter_dev_eq_zero {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    [MeasurableSpace M] {Φ : Flow ℝ≥0 M} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ≥0 m0} {X : ℝ≥0 → Ω → M} {w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0}
    (hX : SatisfiesStandingAssumption Φ P ℱ X w) (δ T : ℝ≥0) (hδ : 0 < δ) (hT : 0 < T) :
    P (⋂ k : ℕ, deviationEvent Φ X (k : ℝ≥0) δ T) = 0 := by
  have hle : ∀ k : ℕ, P.real (⋂ k : ℕ, deviationEvent Φ X (k : ℝ≥0) δ T) ≤ (w k δ T : ℝ) := by
    intro k
    have := measure_inter_dev_le hX k δ T hδ hT Set.univ MeasurableSet.univ
    simp only [Set.univ_inter, probReal_univ, mul_one] at this
    exact le_trans (measureReal_mono (Set.iInter_subset _ k)) this
  have ht : Filter.Tendsto (fun k : ℕ => (w k δ T : ℝ)) Filter.atTop (nhds 0) := by
    have := (NNReal.tendsto_coe.2 (hX.tendsto_w δ T hδ hT)).comp tendsto_natCast_atTop_atTop
    exact this
  have h0 : P.real (⋂ k : ℕ, deviationEvent Φ X (k : ℝ≥0) δ T) ≤ 0 := ge_of_tendsto' ht hle
  have h1 := le_antisymm h0 measureReal_nonneg
  rwa [measureReal_eq_zero_iff] at h1

/-- A positive-probability visit after `t₀` happens with positive probability at a fixed time. -/
theorem exists_pos_time {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    (P : Measure Ω) (X : ℝ≥0 → Ω → M) (hcont : ∀ ω, Continuous fun t => X t ω)
    (U : Set M) (hU : IsOpen U) (t₀ : ℝ≥0)
    (hpos : 0 < P {ω | ∃ s : ℝ≥0, t₀ ≤ s ∧ X s ω ∈ U}) :
    ∃ d : ℝ≥0, t₀ ≤ d ∧ 0 < P {ω | X d ω ∈ U} := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  by_contra hcon
  push_neg at hcon
  have hsub : {ω | ∃ s : ℝ≥0, t₀ ≤ s ∧ X s ω ∈ U} ⊆ ⋃ d ∈ S ∩ Set.Ici t₀, {ω | X d ω ∈ U} := by
    rintro ω ⟨s, hs, hsU⟩
    have hV : IsOpen {r : ℝ≥0 | X r ω ∈ U} := hU.preimage (hcont ω)
    have hcl : s ∈ closure (Set.Ioi t₀) := by rw [closure_Ioi]; exact hs
    obtain ⟨r, hrV, hrI⟩ := mem_closure_iff.1 hcl _ hV hsU
    obtain ⟨d, ⟨hdV, hdI⟩, hdS⟩ := hSd.inter_open_nonempty _ (hV.inter isOpen_Ioi) ⟨r, hrV, hrI⟩
    exact Set.mem_biUnion ⟨hdS, (Set.mem_Ioi.1 hdI).le⟩ hdV
  have hnull : P (⋃ d ∈ S ∩ Set.Ici t₀, {ω | X d ω ∈ U}) = 0 :=
    (measure_biUnion_null_iff (hSc.mono Set.inter_subset_left)).2
      fun d hd => le_antisymm (hcon d hd.2) bot_le
  exact absurd (lt_of_lt_of_le hpos (le_trans (measure_mono hsub) hnull.le)) (lt_irrefl 0)

end SAD376200c5

open MeasureTheory NNReal ENNReal StochApproxDyn.Attractor in
theorem solution {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    [LocallyCompactSpace M] [MeasurableSpace M] [BorelSpace M] (Φ : Flow ℝ≥0 M) (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M)
    (w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0) (hX : SatisfiesStandingAssumption Φ P ℱ X w) (A : Set M)
    (hA : StochApproxDyn.LimitSet.IsAttractor Φ A) (hAtt : (attainableSet P X ∩ StochApproxDyn.LimitSet.basin Φ A).Nonempty) :
    0 < P {ω | StochApproxDyn.LimitSet.limitSet (fun t => X t ω) ⊆ A} := by
  obtain ⟨hAne, hAcpt, -, W, hWn, hattr⟩ := hA
  have hAc : IsClosed A := hAcpt.isClosed
  obtain ⟨ε, hε, hthick⟩ := hAcpt.exists_thickening_subset_open isOpen_interior
    (subset_interior_iff_mem_nhdsSet.2 hWn)
  have hW : ∀ x, Metric.infDist x A < ε → x ∈ W := fun x hx =>
    interior_subset (hthick ((Metric.mem_thickening_iff_infDist_lt hAne).2 hx))
  obtain ⟨t₁, ht₁⟩ := hattr (ε / 2) (by positivity)
  obtain ⟨p, hpAtt, hpB⟩ := hAtt
  have hev : ∀ᶠ t in Filter.atTop, Metric.infDist (Φ t p) A < ε :=
    (hpB : Filter.Tendsto (fun t : ℝ≥0 => Metric.infDist (Φ t p) A) Filter.atTop (nhds 0)).eventually
      (gt_mem_nhds hε)
  obtain ⟨tp, htp⟩ := Filter.eventually_atTop.1 hev
  set U : Set M := {y | Metric.infDist (Φ tp y) A < ε} with hUdef
  have hUo : IsOpen U :=
    isOpen_lt ((Metric.continuous_infDist_pt A).comp (Φ.continuous continuous_const continuous_id))
      continuous_const
  have hpU : p ∈ U := htp tp le_rfl
  have hU : ∀ y ∈ U, ∀ t : ℝ≥0, tp + t₁ ≤ t → Metric.infDist (Φ t y) A < ε / 2 := by
    intro y hy t ht
    have h1 : t = (t - tp) + tp := (tsub_add_cancel_of_le (le_trans le_self_add ht)).symm
    rw [h1, Φ.map_add]
    exact ht₁ _ (le_tsub_of_add_le_left ht) _ (hW _ hy)
  set τ : ℝ≥0 := tp + t₁ + 1 with hτdef
  have hτ : 0 < τ := by positivity
  set δ : ℝ≥0 := ⟨ε / 2, by positivity⟩ with hδdef
  have hδ : 0 < δ := by rw [← NNReal.coe_pos]; show 0 < ε / 2; positivity
  set T : ℝ≥0 := 2 * τ with hTdef
  have hT : 0 < T := by positivity
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1
    ((hX.tendsto_w δ T hδ hT).eventually (gt_mem_nhds zero_lt_one))
  set t₀ : ℝ≥0 := max a 1 with ht₀def
  have ht₀ : 0 < t₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨d, hd, hPd⟩ := SAD376200c5.exists_pos_time P X hX.continuous_path U hUo t₀ (hpAtt t₀ ht₀ U hUo hpU)
  set G : Set Ω := {ω | X d ω ∈ U} with hGdef
  have hG : MeasurableSet[ℱ d] G := (hX.adapted d) hUo.measurableSet
  set D := deviationEvent Φ X d δ T with hDdef
  have hD : MeasurableSet D := hX.measurableSet_deviationEvent d δ T hδ hT
  have hwd : w d δ T < 1 := ha d (le_trans (le_max_left _ _) hd)
  have hwd' : (w d δ T : ℝ) < 1 := by exact_mod_cast hwd
  have hle := SAD376200c5.measure_inter_dev_le hX d δ T hδ hT G hG
  have hGD : 0 < P (G \ D) := by
    rw [pos_iff_ne_zero]
    intro h0
    have hsum := measure_inter_add_sdiff G hD (μ := P)
    rw [h0, add_zero] at hsum
    have hreal : P.real (G ∩ D) = P.real G := by simp [Measure.real, hsum]
    have hGpos : 0 < P.real G := ENNReal.toReal_pos hPd.ne' (measure_ne_top _ _)
    nlinarith
  set Z : Set Ω := ⋃ n : ℕ, ⋃ m : ℕ,
    ⋂ k : ℕ, deviationEvent Φ X (k : ℝ≥0) (1 / ((n : ℝ≥0) + 1)) ((m : ℝ≥0) + 1) with hZdef
  have hZ : P Z = 0 :=
    measure_iUnion_null fun n => measure_iUnion_null fun m =>
      SAD376200c5.measure_iInter_dev_eq_zero hX _ _ (by positivity) (by positivity)
  have hpos : 0 < P ((G \ D) \ Z) := by rwa [measure_sdiff_null hZ]
  refine lt_of_lt_of_le hpos (measure_mono ?_)
  rintro ω ⟨⟨hωG, hωD⟩, hωZ⟩
  refine SAD376200c5.det_limitSet_subset Φ A W hAne hAc ε hW hattr (fun t => X t ω) d τ hτ ?_ ?_ ?_ ?_
  · intro t ht
    exact hU _ hωG t (le_trans le_self_add ht)
  · intro y hy
    exact ht₁ τ (le_trans le_add_self (le_self_add)) y hy
  · intro r hr h hh
    exact SAD376200c5.dev_lt Φ X d δ T ω hωD r hr h hh
  · intro T' hT' η hη
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
    obtain ⟨m, hm⟩ := exists_nat_ge T'
    have hnZ : ω ∉ ⋂ k : ℕ, deviationEvent Φ X (k : ℝ≥0) (1 / ((n : ℝ≥0) + 1)) ((m : ℝ≥0) + 1) :=
      fun h => hωZ (Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨m, h⟩⟩)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ω ∉ deviationEvent Φ X (k : ℝ≥0) (1 / ((n : ℝ≥0) + 1))
        ((m : ℝ≥0) + 1) := by
      simpa [Set.mem_iInter] using hnZ
    refine ⟨k, fun t ht h hh => lt_of_lt_of_le (SAD376200c5.dev_lt Φ X _ _ _ ω hk t ht h
      (le_trans hh (le_trans hm le_self_add))) ?_⟩
    push_cast
    exact hn.le
