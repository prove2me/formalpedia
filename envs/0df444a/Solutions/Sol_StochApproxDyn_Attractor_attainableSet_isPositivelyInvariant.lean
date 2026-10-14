-- Prove2me | solution 1 for StochApproxDyn.Attractor.attainableSet_isPositivelyInvariant
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:21:37.560522+00:00
-- url     : https://prove2.me/submissions/2b959cc9-af19-4c28-8082-e2b3db4485a9

import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics
import Definitions.Def_StochApproxDyn_Attractor_Process

open scoped NNReal ENNReal
open MeasureTheory


namespace StochApproxDyn.Attractor

theorem d41_key {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [MeasurableSpace M]
    {Φ : Flow ℝ≥0 M} {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ≥0 m0}
    {X : ℝ≥0 → Ω → M} {w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0}
    (hX : SatisfiesStandingAssumption Φ P ℱ X w) (q δ T : ℝ≥0) (hδ : 0 < δ) (hT : 0 < T)
    (F : Set Ω) (hF : MeasurableSet[ℱ q] F) :
    P (F ∩ deviationEvent Φ X q δ T) ≤ ENNReal.ofReal (w q δ T) * P F := by
  have hD : MeasurableSet (deviationEvent Φ X q δ T) :=
    hX.measurableSet_deviationEvent q δ T hδ hT
  have hF0 : MeasurableSet F := ℱ.le q _ hF
  have hint : Integrable ((deviationEvent Φ X q δ T).indicator fun _ => (1:ℝ)) P :=
    (integrable_const (1:ℝ)).indicator hD
  have h1 : ∫ ω in F, (deviationEvent Φ X q δ T).indicator (fun _ => (1:ℝ)) ω ∂P
      = P.real (deviationEvent Φ X q δ T ∩ F) := by
    rw [integral_indicator_const _ hD, smul_eq_mul, mul_one, measureReal_restrict_apply hD]
  have h2 := setIntegral_condExp (ℱ.le q) hint hF
  have h3 : ∫ ω in F, (P[(deviationEvent Φ X q δ T).indicator (fun _ => (1:ℝ)) | ℱ q]) ω ∂P
      ≤ ∫ ω in F, (w q δ T : ℝ) ∂P := by
    apply setIntegral_mono_ae_restrict integrable_condExp.integrableOn (integrableOn_const)
    exact ae_restrict_of_ae (hX.condProb_le q δ T hδ hT)
  rw [h2, h1, setIntegral_const, smul_eq_mul] at h3
  rw [Set.inter_comm, ← ofReal_measureReal, ← ofReal_measureReal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  linarith


theorem d41_ofReal_bound (a b c : ℝ≥0∞) (w : ℝ) (hw : 0 ≤ w) (ha : a ≠ ∞)
    (hc : c ≤ ENNReal.ofReal w * a) (hab : a ≤ c + b) : ENNReal.ofReal (1 - w) * a ≤ b := by
  rw [ENNReal.ofReal_sub _ hw, ENNReal.ofReal_one, ENNReal.sub_mul (fun _ _ => ha), one_mul,
    tsub_le_iff_right]
  calc a ≤ c + b := hab
    _ ≤ ENNReal.ofReal w * a + b := add_le_add hc le_rfl
    _ = b + ENNReal.ofReal w * a := add_comm _ _

/-- dyadic grid -/
noncomputable def d41_grid (t : ℝ≥0) (n k : ℕ) : ℝ≥0 := t + (k : ℝ≥0) / 2 ^ n

theorem d41_grid_mono (t : ℝ≥0) (n : ℕ) : Monotone (d41_grid t n) := by
  intro i j hij
  unfold d41_grid
  gcongr

theorem d41_grid_succ (t : ℝ≥0) (n k : ℕ) : d41_grid t (n+1) (2*k) = d41_grid t n k := by
  unfold d41_grid
  congr 1
  rw [pow_succ]
  push_cast
  field_simp

theorem d41_hit_bound {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [MeasurableSpace M]
    [BorelSpace M]
    {Φ : Flow ℝ≥0 M} {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ≥0 m0}
    {X : ℝ≥0 → Ω → M} {w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0}
    (hX : SatisfiesStandingAssumption Φ P ℱ X w) (V : Set M) (hV : IsOpen V)
    (t δ T : ℝ≥0) (hδ : 0 < δ) (hT : 0 < T) (G N : Set Ω) (hN : P N = 0)
    (hG : ∀ ω, ω ∉ N → ∀ g, t ≤ g → X g ω ∈ V → ω ∉ deviationEvent Φ X g δ T → ω ∈ G) :
    ENNReal.ofReal (1 - (w t δ T : ℝ)) * P {ω | ∃ s : ℝ≥0, t ≤ s ∧ X s ω ∈ V} ≤ P G := by
  classical
  set E : ℕ → ℕ → Set Ω := fun n k => {ω | X (d41_grid t n k) ω ∈ V} with hE
  set H : ℕ → ℕ → Set Ω := fun n k => E n k ∩ ⋂ i ∈ Finset.range k, (E n i)ᶜ with hH
  have hEm : ∀ n k, MeasurableSet[ℱ (d41_grid t n k)] (E n k) := fun n k =>
    (hX.adapted _) hV.measurableSet
  have hHm : ∀ n k, MeasurableSet[ℱ (d41_grid t n k)] (H n k) := by
    intro n k
    refine (hEm n k).inter ?_
    refine MeasurableSet.biInter (Set.to_countable _) fun i hi => ?_
    have := ℱ.mono (d41_grid_mono t n (Finset.mem_range.1 hi).le) _ (hEm n i)
    exact this.compl
  have hHm0 : ∀ n k, MeasurableSet (H n k) := fun n k => ℱ.le _ _ (hHm n k)
  have hD : ∀ n k, MeasurableSet (deviationEvent Φ X (d41_grid t n k) δ T) := fun n k =>
    hX.measurableSet_deviationEvent _ δ T hδ hT
  have hdisj : ∀ n, Pairwise (fun i j => Disjoint (H n i) (H n j)) := by
    intro n i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · rw [Set.disjoint_left]
      rintro ω ⟨hi, -⟩ ⟨-, hj⟩
      simp only [Set.mem_iInter] at hj
      exact hj i (Finset.mem_range.2 h) hi
    · rw [Set.disjoint_left]
      rintro ω ⟨-, hi⟩ ⟨hj, -⟩
      simp only [Set.mem_iInter] at hi
      exact hi j (Finset.mem_range.2 h) hj
  have hUnion : ∀ n, (⋃ k, H n k) = ⋃ k, E n k := by
    intro n
    apply Set.Subset.antisymm
    · exact Set.iUnion_mono fun k => Set.inter_subset_left
    · intro ω hω
      have hex : ∃ k, ω ∈ E n k := Set.mem_iUnion.1 hω
      refine Set.mem_iUnion.2 ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
      simp only [Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff]
      intro i hi
      exact Nat.find_min hex hi
  -- bound for each n
  have hn : ∀ n, ENNReal.ofReal (1 - (w t δ T : ℝ)) * P (⋃ k, E n k) ≤ P G := by
    intro n
    rw [← hUnion n, measure_iUnion (hdisj n) (hHm0 n), ← ENNReal.tsum_mul_left]
    calc ∑' k, ENNReal.ofReal (1 - (w t δ T : ℝ)) * P (H n k)
        ≤ ∑' k, P (H n k \ deviationEvent Φ X (d41_grid t n k) δ T) := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          refine d41_ofReal_bound _ _ (P (H n k ∩ deviationEvent Φ X (d41_grid t n k) δ T))
            _ (by positivity) (measure_ne_top _ _) ?_ ?_
          · calc P (H n k ∩ deviationEvent Φ X (d41_grid t n k) δ T)
                ≤ ENNReal.ofReal (w (d41_grid t n k) δ T) * P (H n k) :=
                  d41_key hX _ δ T hδ hT _ (hHm n k)
              _ ≤ ENNReal.ofReal (w t δ T) * P (H n k) := by
                  gcongr
                  exact hX.antitone_w δ T hδ hT (by unfold d41_grid; exact le_self_add)
          · calc P (H n k) = P (H n k ∩ deviationEvent Φ X (d41_grid t n k) δ T ∪
                  H n k \ deviationEvent Φ X (d41_grid t n k) δ T) := by
                    rw [Set.inter_union_diff]
              _ ≤ _ := measure_union_le _ _
      _ = P (⋃ k, H n k \ deviationEvent Φ X (d41_grid t n k) δ T) := by
          rw [measure_iUnion]
          · intro i j hij
            exact Disjoint.mono Set.diff_subset Set.diff_subset (hdisj n hij)
          · exact fun k => (hHm0 n k).diff (hD n k)
      _ ≤ P (G ∪ N) := by
          apply measure_mono
          intro ω hω
          obtain ⟨k, hk, hkD⟩ := Set.mem_iUnion.1 hω
          by_cases hωN : ω ∈ N
          · exact Or.inr hωN
          · exact Or.inl (hG ω hωN _ (by unfold d41_grid; exact le_self_add) hk.1 hkD)
      _ ≤ P G + P N := measure_union_le _ _
      _ = P G := by rw [hN, add_zero]
  -- monotone in n
  have hmono : Monotone (fun n => ⋃ k, E n k) := by
    apply monotone_nat_of_le_succ
    intro n ω hω
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hω
    refine Set.mem_iUnion.2 ⟨2 * k, ?_⟩
    simp only [hE, Set.mem_setOf_eq, d41_grid_succ] at hk ⊢
    exact hk
  have hsub : {ω | ∃ s : ℝ≥0, t ≤ s ∧ X s ω ∈ V} ⊆ ⋃ n, ⋃ k, E n k := by
    rintro ω ⟨s, hts, hs⟩
    have hopen : IsOpen ((fun u => X u ω) ⁻¹' V) := hV.preimage (hX.continuous_path ω)
    obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hopen s hs
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (1/2 : ℝ) < 1)
    set k := ⌊((s - t : ℝ≥0) * 2 ^ n)⌋₊ with hk
    refine Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨k, ?_⟩⟩
    show X (d41_grid t n k) ω ∈ V
    apply hball
    have h2pos : (0 : ℝ≥0) < 2 ^ n := by positivity
    have hk1 : (k : ℝ≥0) ≤ (s - t) * 2 ^ n := Nat.floor_le (by positivity)
    have hk2 : (s - t) * 2 ^ n < (k : ℝ≥0) + 1 := Nat.lt_floor_add_one _
    have hk1' : (k : ℝ≥0) / 2 ^ n ≤ s - t := by rwa [div_le_iff₀ h2pos]
    have hk2' : s - t < (k : ℝ≥0) / 2 ^ n + 1 / 2 ^ n := by
      rw [← add_div, lt_div_iff₀ h2pos]; exact hk2
    have hst : (s - t : ℝ≥0) + t = s := tsub_add_cancel_of_le hts
    rw [Metric.mem_ball, NNReal.dist_eq]
    unfold d41_grid
    have e1 : ((s - t : ℝ≥0) : ℝ) = (s : ℝ) - t := NNReal.coe_sub hts
    have hk1r : ((k : ℝ≥0) / 2 ^ n : ℝ≥0) ≤ ((s - t : ℝ≥0) : ℝ) := by exact_mod_cast hk1'
    have hk2r : ((s - t : ℝ≥0) : ℝ) < ((k : ℝ≥0) / 2 ^ n : ℝ≥0) + ((1 / 2 ^ n : ℝ≥0) : ℝ) := by
      exact_mod_cast hk2'
    have hpow : ((1 / 2 ^ n : ℝ≥0) : ℝ) = (1/2 : ℝ) ^ n := by push_cast; rw [one_div_pow]
    rw [hpow] at hk2r
    push_cast at hk1r hk2r e1 ⊢
    rw [abs_lt]
    constructor <;> linarith
  calc ENNReal.ofReal (1 - (w t δ T : ℝ)) * P {ω | ∃ s : ℝ≥0, t ≤ s ∧ X s ω ∈ V}
      ≤ ENNReal.ofReal (1 - (w t δ T : ℝ)) * P (⋃ n, ⋃ k, E n k) := by
        gcongr
    _ = ⨆ n, ENNReal.ofReal (1 - (w t δ T : ℝ)) * P (⋃ k, E n k) := by
        rw [hmono.measure_iUnion, ENNReal.mul_iSup]
    _ ≤ P G := iSup_le hn


theorem d41_edist_lt_of_not_dev {Ω M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (X : ℝ≥0 → Ω → M) (g δ T : ℝ≥0) (ω : Ω) (hω : ω ∉ deviationEvent Φ X g δ T)
    (s h : ℝ≥0) (hs : g ≤ s) (hh : h ≤ T) : edist (X (s + h) ω) (Φ h (X s ω)) < δ := by
  simp only [deviationEvent, Set.mem_setOf_eq, not_le] at hω
  refine lt_of_le_of_lt ?_ hω
  refine le_trans ?_ (le_iSup₂ (f := fun s (_ : g ≤ s) =>
    ⨆ (h : ℝ≥0) (_ : h ≤ T), edist (X (s + h) ω) (Φ h (X s ω))) s hs)
  exact le_iSup₂ (f := fun h (_ : h ≤ T) => edist (X (s + h) ω) (Φ h (X s ω))) h hh

theorem d41_dist_lt_of_not_dev {Ω M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (X : ℝ≥0 → Ω → M) (g δ T : ℝ≥0) (ω : Ω) (hω : ω ∉ deviationEvent Φ X g δ T)
    (s h : ℝ≥0) (hs : g ≤ s) (hh : h ≤ T) : dist (X (s + h) ω) (Φ h (X s ω)) < δ := by
  have := d41_edist_lt_of_not_dev Φ X g δ T ω hω s h hs hh
  rw [edist_lt_coe] at this
  exact_mod_cast this

theorem attainable_core {Ω M : Type*} {m0 : MeasurableSpace Ω}
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] (Φ : Flow ℝ≥0 M) (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M)
    (w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0) (hX : SatisfiesStandingAssumption Φ P ℱ X w) :
    IsPositivelyInvariant Φ (attainableSet P X) := by
  rintro t0 _ ⟨p, hp, rfl⟩
  intro t ht U hU hpU
  rcases eq_zero_or_pos t0 with h0 | h0
  · subst h0
    rw [Flow.map_zero_apply] at hpU
    exact hp t ht U hU hpU
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU _ hpU
  have hcont : Continuous (Φ t0) := Φ.continuous_toFun t0
  obtain ⟨r, hr, hrε⟩ := Metric.continuous_iff.1 hcont p (ε/2) (by positivity)
  set δ : ℝ≥0 := ⟨ε/2, by positivity⟩ with hδdef
  have hδ : 0 < δ := by rw [← NNReal.coe_pos]; show (0:ℝ) < ε/2; positivity
  have htend := hX.tendsto_w δ t0 hδ h0
  obtain ⟨t', ht'⟩ := Filter.eventually_atTop.1
    ((htend.eventually (gt_mem_nhds (by norm_num : (0:ℝ≥0) < 1))))
  set t'' := max t t' with ht''
  have hw1 : w t'' δ t0 < 1 := ht' t'' (le_max_right _ _)
  have hpos1 : 0 < P {ω | ∃ s : ℝ≥0, t'' ≤ s ∧ X s ω ∈ Metric.ball p r} :=
    hp t'' (lt_of_lt_of_le ht (le_max_left _ _)) _ Metric.isOpen_ball (Metric.mem_ball_self hr)
  have key := d41_hit_bound hX (Metric.ball p r) Metric.isOpen_ball t'' δ t0 hδ h0
    {ω | ∃ s : ℝ≥0, t ≤ s ∧ X s ω ∈ U} ∅ measure_empty ?_
  · refine lt_of_lt_of_le (ENNReal.mul_pos ?_ hpos1.ne') key
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_pos]
    exact_mod_cast hw1
  · intro ω _ g hg hgV hgD
    refine ⟨g + t0, le_trans (le_max_left _ _) (le_trans hg le_self_add), hεU ?_⟩
    have h1 := d41_dist_lt_of_not_dev Φ X g δ t0 ω hgD g t0 le_rfl le_rfl
    have h2 := hrε (X g ω) hgV
    rw [Metric.mem_ball]
    have : (δ : ℝ) = ε / 2 := rfl
    calc dist (X (g + t0) ω) (Φ t0 p) ≤ dist (X (g + t0) ω) (Φ t0 (X g ω)) +
          dist (Φ t0 (X g ω)) (Φ t0 p) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by rw [← this]; exact add_lt_add h1 h2
      _ = ε := by ring

end StochApproxDyn.Attractor

open StochApproxDyn.Attractor


theorem solution {Ω M : Type*} {m0 : MeasurableSpace Ω}
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] (Φ : Flow ℝ≥0 M) (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M)
    (w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0) (hX : SatisfiesStandingAssumption Φ P ℱ X w) :
    IsPositivelyInvariant Φ (attainableSet P X) := by
  exact attainable_core Φ P ℱ X w hX
