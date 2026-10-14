-- Prove2me | solution 1 for StochApproxDyn.Attractor.measure_limitSet_subset_ge
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:26:11.985215+00:00
-- url     : https://prove2.me/submissions/902ee4ce-4338-4f16-be1e-9326d6e21660

import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics
import Definitions.Def_StochApproxDyn_Attractor_Process

open scoped NNReal ENNReal
open MeasureTheory

universe u v


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

open StochApproxDyn.LimitSet Metric in
theorem stepdev_core {M : Type*} [MetricSpace M] [LocallyCompactSpace M]
    (Φ : Flow ℝ≥0 M) (A : Set M) (hA : StochApproxDyn.LimitSet.IsAttractor Φ A) (K : Set M)
    (hKne : K.Nonempty)
    (hK : IsCompact K) (hKB : K ⊆ StochApproxDyn.LimitSet.basin Φ A) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ X : ℝ≥0 → M, StochApproxDyn.LimitSet.IsAsymptoticPseudotrajectory Φ X → X 0 ∈ K →
        stepDeviation Φ X T < (δ : ℝ≥0∞) → StochApproxDyn.LimitSet.limitSet X ⊆ A := by
  obtain ⟨hAne, hAc, -, W, hW, hatt⟩ := hA
  obtain ⟨r0, hr0, hthick⟩ := hAc.exists_thickening_subset_open isOpen_interior
    (subset_interior_iff_mem_nhdsSet.2 hW)
  have hNW : ∀ x, infDist x A < r0 → x ∈ W := fun x hx =>
    interior_subset (hthick ((mem_thickening_iff_infDist_lt hAne).2 hx))
  obtain ⟨T1, hT1⟩ := hatt (r0/4) (by positivity)
  have hcontτ : ∀ τ : ℝ≥0, Continuous fun y => infDist (Φ τ y) A := fun τ =>
    (continuous_infDist_pt A).comp (Φ.continuous_toFun τ)
  have hcov : K ⊆ ⋃ τ : ℝ≥0, {y | infDist (Φ τ y) A < r0} := by
    intro x hx
    have := hKB hx
    obtain ⟨τ, hτ⟩ := (this.eventually (gt_mem_nhds hr0)).exists
    exact Set.mem_iUnion.2 ⟨τ, hτ⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover _ (fun τ => isOpen_lt (hcontτ τ) continuous_const) hcov
  set T : ℝ≥0 := F.sup id + T1 + 1 with hTdef
  have hTpos : 0 < T := by positivity
  have hT1T : T1 ≤ T := by rw [hTdef]; calc T1 ≤ F.sup id + T1 := le_add_self
                                          _ ≤ _ := le_self_add
  have hKT : ∀ y ∈ K, infDist (Φ T y) A < r0/4 := by
    intro y hy
    obtain ⟨τ, hτF, hτ⟩ := Set.mem_iUnion₂.1 (hF hy)
    have hτle : τ ≤ F.sup id := Finset.le_sup (f := id) hτF
    have hsplit : T = (T - τ) + τ := (tsub_add_cancel_of_le (by
      rw [hTdef]; calc τ ≤ F.sup id := hτle
                    _ ≤ F.sup id + T1 + 1 := by rw [add_assoc]; exact le_self_add)).symm
    rw [hsplit, Flow.map_add]
    apply hT1 (T - τ) _ _ (hNW _ hτ)
    rw [le_tsub_iff_right (by rw [hTdef]; calc τ ≤ F.sup id := hτle
                    _ ≤ F.sup id + T1 + 1 := by rw [add_assoc]; exact le_self_add), hTdef]
    calc T1 + τ ≤ T1 + F.sup id := add_le_add le_rfl hτle
      _ = F.sup id + T1 := add_comm _ _
      _ ≤ _ := le_self_add
  have hWT : ∀ y ∈ W, infDist (Φ T y) A < r0/4 := fun y hy => hT1 T hT1T y hy
  set δ : ℝ≥0 := ⟨r0/2, by positivity⟩ with hδdef
  have hδ : 0 < δ := by rw [← NNReal.coe_pos]; show (0:ℝ) < r0/2; positivity
  refine ⟨T, hTpos, δ, hδ, ?_⟩
  intro X hX hX0 hdev
  have step : ∀ k : ℕ, dist (Φ T (X (k*T))) (X (k*T + T)) < r0/2 := by
    intro k
    have h1 : edist (Φ T (X (k*T))) (X (k*T + T)) < δ :=
      lt_of_le_of_lt (le_iSup (fun k : ℕ => edist (Φ T (X (k*T))) (X (k*T + T))) k) hdev
    rw [edist_lt_coe] at h1
    exact_mod_cast h1
  have hKW : ∀ k : ℕ, X (k*T) ∈ K ∨ X (k*T) ∈ W := by
    intro k
    induction k with
    | zero => left; simpa using hX0
    | succ j ih =>
      right
      apply hNW
      have e : (((j+1 : ℕ) : ℝ≥0) * T) = j * T + T := by push_cast; ring
      rw [e]
      have h2 : infDist (Φ T (X (j*T))) A < r0/4 := by
        rcases ih with h | h
        · exact hKT _ h
        · exact hWT _ h
      calc infDist (X (j*T + T)) A ≤ infDist (Φ T (X (j*T))) A + dist (X (j*T + T)) (Φ T (X (j*T))) :=
            infDist_le_infDist_add_dist
        _ < r0/4 + r0/2 := add_lt_add h2 (by rw [dist_comm]; exact step j)
        _ < r0 := by linarith
  have hW1 : ∀ j : ℕ, X ((j + 1) * T) ∈ W := by
    intro j
    have := hKW (j+1)
    have e : (((j+1 : ℕ) : ℝ≥0) * T) = (j + 1) * T := by push_cast; ring
    rw [e] at this
    rcases this with h | h
    · -- also in W via the inductive argument; recompute
      apply hNW
      have e2 : ((j : ℝ≥0) + 1) * T = j * T + T := by ring
      rw [e2]
      have h2 : infDist (Φ T (X (j*T))) A < r0/4 := by
        rcases hKW j with h | h
        · exact hKT _ h
        · exact hWT _ h
      calc infDist (X (j*T + T)) A ≤ infDist (Φ T (X (j*T))) A + dist (X (j*T + T)) (Φ T (X (j*T))) :=
            infDist_le_infDist_add_dist
        _ < r0/4 + r0/2 := add_lt_add h2 (by rw [dist_comm]; exact step j)
        _ < r0 := by linarith
    · exact h
  -- eventually close to A
  have hev : ∀ ε : ℝ, 0 < ε → ∃ s0 : ℝ≥0, ∀ s : ℝ≥0, s0 ≤ s → infDist (X s) A < ε := by
    intro ε hε
    obtain ⟨Tε, hTε⟩ := hatt (ε/2) (by positivity)
    obtain ⟨t₀, ht₀⟩ := hX.2 (Tε + T) (by positivity) (ε/2) (by positivity)
    refine ⟨t₀ + Tε + T, fun s hs => ?_⟩
    have hTεs : Tε ≤ s := le_trans (by calc Tε ≤ t₀ + Tε := le_add_self
                                          _ ≤ t₀ + Tε + T := le_self_add) hs
    set u : ℝ≥0 := s - Tε with hu
    have hur : (u : ℝ) = s - Tε := NNReal.coe_sub hTεs
    set k := ⌊u / T⌋₊ with hk
    have hk1 : (k : ℝ≥0) * T ≤ u := by
      have := Nat.floor_le (a := u / T) (by positivity)
      rwa [le_div_iff₀ hTpos] at this
    have hk2 : u < ((k : ℝ≥0) + 1) * T := by
      have := Nat.lt_floor_add_one (u / T)
      rwa [div_lt_iff₀ hTpos] at this
    have hsr : (t₀ : ℝ) + Tε + T ≤ s := by exact_mod_cast hs
    have hk1r : (k : ℝ) * T ≤ s - Tε := by rw [← hur]; exact_mod_cast hk1
    have hk2r : s - Tε < ((k : ℝ) + 1) * T := by rw [← hur]; exact_mod_cast hk2
    have hTr : (0:ℝ) < T := by exact_mod_cast hTpos
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := by
      rcases Nat.eq_zero_or_eq_succ_pred k with h | h
      · exfalso
        rw [h] at hk2r
        simp at hk2r
        have : (0:ℝ) ≤ t₀ := t₀.2
        linarith
      · exact ⟨_, h⟩
    rw [hj] at hk1r hk2r
    have hkle : ((j + 1 : ℕ) : ℝ≥0) * T ≤ s := by
      have : ((j + 1 : ℕ) : ℝ) * T ≤ s := by linarith [Tε.2]
      exact_mod_cast this
    set S' : ℝ≥0 := s - ((j + 1 : ℕ) : ℝ≥0) * T with hS'
    have hS'r : (S' : ℝ) = s - ((j + 1 : ℕ) : ℝ) * T := by
      rw [hS', NNReal.coe_sub hkle]; push_cast; ring
    have hS'1 : Tε ≤ S' := by
      have : (Tε : ℝ) ≤ S' := by rw [hS'r]; linarith
      exact_mod_cast this
    have hS'2 : S' ≤ Tε + T := by
      have : (S' : ℝ) ≤ Tε + T := by
        rw [hS'r]; push_cast at hk2r ⊢; linarith
      exact_mod_cast this
    have ht0k : t₀ ≤ ((j + 1 : ℕ) : ℝ≥0) * T := by
      have : (t₀ : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * T := by push_cast at hk2r ⊢; linarith
      exact_mod_cast this
    have hsum : ((j + 1 : ℕ) : ℝ≥0) * T + S' = s := add_tsub_cancel_of_le hkle
    have hd := ht₀ _ ht0k S' hS'2
    rw [hsum] at hd
    have hinW : X (((j + 1 : ℕ) : ℝ≥0) * T) ∈ W := by
      have := hW1 j; push_cast; exact this
    have ha := hTε S' hS'1 _ hinW
    calc infDist (X s) A ≤ infDist (Φ S' (X (((j + 1 : ℕ) : ℝ≥0) * T))) A +
          dist (X s) (Φ S' (X (((j + 1 : ℕ) : ℝ≥0) * T))) := infDist_le_infDist_add_dist
      _ < ε/2 + ε/2 := add_lt_add ha hd
      _ = ε := by ring
  intro p hp
  rw [hAc.isClosed.mem_iff_infDist_zero hAne]
  by_contra hne
  have hpos : 0 < infDist p A := lt_of_le_of_ne infDist_nonneg (Ne.symm hne)
  obtain ⟨s0, hs0⟩ := hev (infDist p A / 2) (by positivity)
  have hcl : closure (X '' Set.Ici s0) ⊆ {y | infDist y A ≤ infDist p A / 2} := by
    apply closure_minimal
    · rintro _ ⟨s, hs, rfl⟩
      exact (hs0 s hs).le
    · exact isClosed_le (continuous_infDist_pt A) continuous_const
  have := hcl (Set.mem_iInter.1 hp s0)
  simp only [Set.mem_setOf_eq] at this
  linarith


open StochApproxDyn.LimitSet in
theorem d41_ae_apt {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [MeasurableSpace M]
    {Φ : Flow ℝ≥0 M} {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ≥0 m0}
    {X : ℝ≥0 → Ω → M} {w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0}
    (hX : SatisfiesStandingAssumption Φ P ℱ X w) :
    P {ω | ¬ IsAsymptoticPseudotrajectory Φ (fun s => X s ω)} = 0 := by
  apply measure_mono_null (t := ⋃ (m : ℕ) (T : ℕ), ⋂ (n : ℕ),
    deviationEvent Φ X (n : ℝ≥0) (1 / ((m : ℝ≥0) + 1)) ((T : ℝ≥0) + 1))
  · intro ω hω
    by_contra hcon
    apply hω
    simp only [Set.mem_iUnion, Set.mem_iInter, not_exists, not_forall] at hcon
    refine ⟨hX.continuous_path ω, fun T hT ε hε => ?_⟩
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨n, hn⟩ := hcon m ⌈T⌉₊
    refine ⟨n, fun t ht h hh => ?_⟩
    have hh' : h ≤ (⌈T⌉₊ : ℝ≥0) + 1 := hh.trans ((Nat.le_ceil T).trans le_self_add)
    have := d41_dist_lt_of_not_dev Φ X n _ _ ω hn t h ht hh'
    have e : ((1 / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) = 1 / ((m : ℝ) + 1) := by push_cast; ring
    rw [e] at this
    linarith
  · refine measure_iUnion_null fun m => measure_iUnion_null fun T => ?_
    apply le_antisymm _ (zero_le)
    have hδ : (0:ℝ≥0) < 1 / ((m : ℝ≥0) + 1) := by positivity
    have hT : (0:ℝ≥0) < (T : ℝ≥0) + 1 := by positivity
    have hb : ∀ n : ℕ, P (⋂ n : ℕ, deviationEvent Φ X (n : ℝ≥0) (1 / ((m : ℝ≥0) + 1))
        ((T : ℝ≥0) + 1)) ≤ (w n (1 / ((m : ℝ≥0) + 1)) ((T : ℝ≥0) + 1) : ℝ≥0∞) := by
      intro n
      refine (measure_mono (Set.iInter_subset _ n)).trans ?_
      have := d41_key hX n _ _ hδ hT Set.univ MeasurableSet.univ
      simpa [ENNReal.ofReal_coe_nnreal] using this
    have ht : Filter.Tendsto (fun n : ℕ => (w n (1 / ((m : ℝ≥0) + 1)) ((T : ℝ≥0) + 1) : ℝ≥0∞))
        Filter.atTop (nhds 0) := by
      have := (hX.tendsto_w _ _ hδ hT).comp tendsto_natCast_atTop_atTop
      have := ENNReal.tendsto_coe.2 this
      simpa using this
    exact ge_of_tendsto' ht hb

open StochApproxDyn.LimitSet in
theorem ge_core {M : Type u} [MetricSpace M] [LocallyCompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (Φ : Flow ℝ≥0 M) (A : Set M) (hA : StochApproxDyn.LimitSet.IsAttractor Φ A)
    (U : Set M) (hU : IsOpen U) (hUc : IsCompact (closure U)) (hUB : closure U ⊆ StochApproxDyn.LimitSet.basin Φ A) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ (Ω : Type v) (m0 : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
        ∀ (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M) (w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0),
          SatisfiesStandingAssumption Φ P ℱ X w →
          ∀ t : ℝ≥0,
            ENNReal.ofReal (1 - (w t δ T : ℝ)) * P {ω | ∃ s : ℝ≥0, t ≤ s ∧ X s ω ∈ U} ≤
              P {ω | StochApproxDyn.LimitSet.limitSet (fun s => X s ω) ⊆ A} := by
  by_cases hUne : U.Nonempty
  · obtain ⟨T, hT, δ, hδ, hmain⟩ := stepdev_core Φ A hA (closure U) hUne.closure hUc hUB
    refine ⟨T, hT, δ, hδ, ?_⟩
    intro Ω m0 P hP ℱ X w hX t
    refine d41_hit_bound hX U hU t δ T hδ hT _ _ (d41_ae_apt hX) ?_
    intro ω hω g hg hgU hgD
    have hapt : IsAsymptoticPseudotrajectory Φ (fun s => X s ω) := by
      simpa using hω
    have hY : IsAsymptoticPseudotrajectory Φ (fun u => X (g + u) ω) := by
      refine ⟨(hX.continuous_path ω).comp (continuous_const.add continuous_id), ?_⟩
      intro T' hT' ε hε
      obtain ⟨t₀, ht₀⟩ := hapt.2 T' hT' ε hε
      refine ⟨t₀, fun u hu h hh => ?_⟩
      show dist (X (g + (u + h)) ω) (Φ h (X (g + u) ω)) < ε
      rw [← add_assoc]
      exact ht₀ (g + u) (le_add_left hu) h hh
    have hY0 : (fun u => X (g + u) ω) 0 ∈ closure U := by
      show X (g + 0) ω ∈ closure U
      rw [add_zero]; exact subset_closure hgU
    have hYdev : stepDeviation Φ (fun u => X (g + u) ω) T < (δ : ℝ≥0∞) := by
      simp only [deviationEvent, Set.mem_setOf_eq, not_le] at hgD
      refine lt_of_le_of_lt (iSup_le fun k => ?_) hgD
      show edist (Φ T (X (g + k * T) ω)) (X (g + (k * T + T)) ω) ≤ _
      rw [edist_comm, ← add_assoc]
      refine le_trans ?_ (le_iSup₂ (f := fun s (_ : g ≤ s) =>
        ⨆ (h : ℝ≥0) (_ : h ≤ T), edist (X (s + h) ω) (Φ h (X s ω))) (g + k * T) le_self_add)
      exact le_iSup₂ (f := fun h (_ : h ≤ T) => edist (X (g + k * T + h) ω)
        (Φ h (X (g + k * T) ω))) T le_rfl
    have hL := hmain _ hY hY0 hYdev
    show limitSet (fun s => X s ω) ⊆ A
    refine subset_trans ?_ hL
    intro p hp
    refine Set.mem_iInter.2 fun u => closure_mono ?_ (Set.mem_iInter.1 hp (g + u))
    rintro _ ⟨s, hs, rfl⟩
    have hs' : g + u ≤ s := hs
    refine ⟨s - g, le_tsub_of_add_le_left hs', ?_⟩
    show X (g + (s - g)) ω = X s ω
    rw [add_tsub_cancel_of_le (le_trans le_self_add hs')]
  · refine ⟨1, one_pos, 1, one_pos, ?_⟩
    intro Ω m0 P hP ℱ X w hX t
    rw [Set.not_nonempty_iff_eq_empty] at hUne
    subst hUne
    simp

end StochApproxDyn.Attractor

open StochApproxDyn.Attractor


theorem solution {M : Type u} [MetricSpace M] [LocallyCompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (Φ : Flow ℝ≥0 M) (A : Set M) (hA : StochApproxDyn.LimitSet.IsAttractor Φ A)
    (U : Set M) (hU : IsOpen U) (hUc : IsCompact (closure U)) (hUB : closure U ⊆ StochApproxDyn.LimitSet.basin Φ A) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ (Ω : Type v) (m0 : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
        ∀ (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M) (w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0),
          SatisfiesStandingAssumption Φ P ℱ X w →
          ∀ t : ℝ≥0,
            ENNReal.ofReal (1 - (w t δ T : ℝ)) * P {ω | ∃ s : ℝ≥0, t ≤ s ∧ X s ω ∈ U} ≤
              P {ω | StochApproxDyn.LimitSet.limitSet (fun s => X s ω) ⊆ A} := by
  exact ge_core Φ A hA U hU hUc hUB
