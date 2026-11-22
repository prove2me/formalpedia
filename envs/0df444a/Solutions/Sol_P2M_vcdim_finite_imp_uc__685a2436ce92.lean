-- Prove2me | solution 1 for P2M_vcdim_finite_imp_uc__685a2436ce92
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:38.364212+00:00
-- url     : https://prove2.me/submissions/cc39d7ed-1c12-47f1-b714-e94061e79ff3

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Theorems.Thm_hoeffding_one_sided
public import Theorems.Thm_hoeffding_one_sided_upper
public import Theorems.Thm_symmetrization_uc_bound
public import Theorems.Thm_growth_exp_le_delta
public import Theorems.Thm_vcdim_finite_imp_growth_bounded

section
@[expose] public section
universe u v
open MeasureTheory ENNReal
private lemma uc_bad_event_le_delta_proved {X : Type u} [MeasurableSpace X] [Infinite X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (v : ℕ) (hv_pos : 0 < v)
    (hv : ∀ (n : ℕ), v ≤ n →
      GrowthFunction X C n ≤ ∑ i ∈ Finset.range (v + 1), Nat.choose n i)
    (hm_bound : (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) / δ ≤ ↑m)
    (hE_nullmeas : MeasureTheory.NullMeasurableSet
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
       (MeasureTheory.Measure.pi (fun _ : Fin m => D)))) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { xs : Fin m → X | ∃ h ∈ C,
        |TrueErrorReal X h c D -
         EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
           (zeroOneLoss Bool)| ≥ ε }
      ≤ ENNReal.ofReal δ := by
  have ⟨h_bound, h_large⟩ := growth_exp_le_delta C v hv_pos m hm ε δ hε hδ hδ1 hv hm_bound
  have h_sym := symmetrization_uc_bound D C c hmeas_C hc_meas m hm ε hε h_large hE_nullmeas
  calc MeasureTheory.Measure.pi (fun _ : Fin m => D)
        { xs : Fin m → X | ∃ h ∈ C,
          |TrueErrorReal X h c D -
           EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
             (zeroOneLoss Bool)| ≥ ε }
      ≤ ENNReal.ofReal (4 * ↑(GrowthFunction X C (2 * m)) *
          Real.exp (-(↑m * ε ^ 2 / 8))) := h_sym
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal h_bound
private theorem bad_event_compl_measure_ge {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (Bad : Set Ω) {δ : ℝ} (hδ : 0 < δ)
    (h_ub : μ Bad ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal (1 - δ) ≤ μ Badᶜ := by
  have h_sub : (1 : ENNReal) ≤ μ Bad + μ Badᶜ := by
    have := MeasureTheory.measure_union_le (μ := μ) Bad Badᶜ
    rwa [Set.union_compl_self, measure_univ] at this
  calc ENNReal.ofReal (1 - δ)
      = 1 - ENNReal.ofReal δ := by rw [ENNReal.ofReal_sub 1 (le_of_lt hδ), ENNReal.ofReal_one]
    _ ≤ 1 - μ Bad := tsub_le_tsub_left h_ub 1
    _ ≤ (μ Bad + μ Badᶜ) - μ Bad := tsub_le_tsub_right h_sub _
    _ = μ Badᶜ := ENNReal.add_sub_cancel_left
        (ne_top_of_le_ne_top ENNReal.one_ne_top MeasureTheory.prob_le_one)
private theorem uniform_good_event_eq_bad_compl {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) (C : ConceptClass X Bool) (c : Concept X Bool)
    (m : ℕ) (ε : ℝ) :
    { xs : Fin m → X | ∀ (h : Concept X Bool), h ∈ C →
        |TrueErrorReal X h c D -
          EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)| < ε } =
      { xs : Fin m → X | ∃ h ∈ C,
        |TrueErrorReal X h c D -
          EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)| ≥ ε }ᶜ := by aesop
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hC : VCDim X C < ⊤)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) :
    HasUniformConvergence X C := by
  rcases finite_or_infinite X with hfin | hinf
  · -- ═══ FINITE X BRANCH ═══
    let := Fintype.ofFinite X
    have : DecidableEq X := Classical.decEq X
    have : Fintype (Concept X Bool) := show Fintype (X → Bool) from Pi.instFintype
    have hfin_C : Set.Finite C := Set.Finite.subset (Set.finite_univ) (Set.subset_univ C)
    set Cf := hfin_C.toFinset with hCf_def
    have hCf_mem : ∀ h, h ∈ Cf ↔ h ∈ C := fun h => Set.Finite.mem_toFinset hfin_C
    set N := Cf.card with hN_def
    intro ε δ hε hδ
    set ε' := min ε 1 with hε'_def
    have hε'_pos : 0 < ε' := lt_min hε one_pos
    have hε'_le_one : ε' ≤ 1 := min_le_right ε 1
    have hε'_le_ε : ε' ≤ ε := min_le_left ε 1
    use max 1 (Nat.ceil ((Real.log (2 * ↑N / δ)) / (2 * ε' ^ 2)))
    intro D hD c m hm
    by_cases hδ1 : 1 ≤ δ
    · have : ENNReal.ofReal (1 - δ) = 0 := ENNReal.ofReal_eq_zero.mpr (by linarith)
      rw [this]; exact zero_le
    · push Not at hδ1
      have hm_pos : 0 < m := Nat.lt_of_lt_of_le (by omega) hm
      have hmeas_fin : ∀ (h' c' : X → Bool),
          Measurable h' → Measurable c' → MeasurableSet {x : X | h' x ≠ c' x} := by
        intro h' c' hh' hc'
        have : {x : X | h' x ≠ c' x} = h' ⁻¹' {true} ∩ c' ⁻¹' {false} ∪
            (h' ⁻¹' {false} ∩ c' ⁻¹' {true}) := by
          ext x; simp [Ne]; cases h' x <;> cases c' x <;> simp
        rw [this]
        exact (hh' (measurableSet_singleton _) |>.inter (hc' (measurableSet_singleton _))).union
          (hh' (measurableSet_singleton _) |>.inter (hc' (measurableSet_singleton _)))
      set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
      set Bad := { xs : Fin m → X | ∃ h ∈ C,
          |TrueErrorReal X h c D -
           EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
             (zeroOneLoss Bool)| ≥ ε }
      have h_ub : μ Bad ≤ ENNReal.ofReal δ := by
        set Bad' := { xs : Fin m → X | ∃ h ∈ C,
            |TrueErrorReal X h c D -
             EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
               (zeroOneLoss Bool)| ≥ ε' }
        have hBad_sub_Bad' : Bad ⊆ Bad' := by
          intro xs hxs; obtain ⟨h', hh', hgap⟩ := hxs
          exact ⟨h', hh', le_trans (by linarith [hε'_le_ε]) hgap⟩
        have hBad'_sub : Bad' ⊆ ⋃ h ∈ Cf, { xs : Fin m → X |
            |TrueErrorReal X h c D -
             EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
               (zeroOneLoss Bool)| ≥ ε' } := by
          intro xs hxs
          simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hxs ⊢
          obtain ⟨h', hh'C, hh'gap⟩ := hxs
          exact ⟨h', (hCf_mem h').mpr hh'C, hh'gap⟩
        have hper_hyp : ∀ h' ∈ Cf, μ { xs : Fin m → X |
            |TrueErrorReal X h' c D -
             EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
               (zeroOneLoss Bool)| ≥ ε' }
            ≤ ENNReal.ofReal (2 * Real.exp (-2 * ↑m * ε' ^ 2)) := by
          intro h' _
          have h_abs_sub : { xs : Fin m → X |
              |TrueErrorReal X h' c D -
               EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                 (zeroOneLoss Bool)| ≥ ε' } ⊆
            { xs : Fin m → X | EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                (zeroOneLoss Bool) ≤ TrueErrorReal X h' c D - ε' } ∪
            { xs : Fin m → X | EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                (zeroOneLoss Bool) ≥ TrueErrorReal X h' c D + ε' } := by
            intro xs hxs
            simp only [Set.mem_ofPred_eq, Set.mem_union] at hxs ⊢
            rcases le_or_gt (EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                (zeroOneLoss Bool)) (TrueErrorReal X h' c D - ε') with h_le | h_gt
            · left; exact h_le
            · right
              set d := TrueErrorReal X h' c D -
                EmpiricalError X Bool h' (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)
              have hd_neg : d ≤ 0 := by
                by_contra hpos
                push Not at hpos
                exact absurd (hxs.trans_eq (abs_of_pos hpos)) (by linarith)
              linarith [hxs.trans_eq (abs_of_nonpos hd_neg)]
          calc μ { xs | |TrueErrorReal X h' c D -
                EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                  (zeroOneLoss Bool)| ≥ ε' }
              ≤ μ ({ xs | EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                  (zeroOneLoss Bool) ≤ TrueErrorReal X h' c D - ε' } ∪
                { xs | EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                  (zeroOneLoss Bool) ≥ TrueErrorReal X h' c D + ε' }) :=
                MeasureTheory.measure_mono h_abs_sub
            _ ≤ μ { xs | EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                  (zeroOneLoss Bool) ≤ TrueErrorReal X h' c D - ε' } +
                μ { xs | EmpiricalError X Bool h' (fun i => (xs i, c (xs i)))
                  (zeroOneLoss Bool) ≥ TrueErrorReal X h' c D + ε' } :=
                MeasureTheory.measure_union_le _ _
            _ ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * ε' ^ 2)) +
                ENNReal.ofReal (Real.exp (-2 * ↑m * ε' ^ 2)) := by
                gcongr
                · exact hoeffding_one_sided D h' c m hm_pos ε' hε'_pos hε'_le_one
                    (hmeas_fin h' c (hc_meas h') (hc_meas c))
                · exact hoeffding_one_sided_upper D h' c m hm_pos ε' hε'_pos hε'_le_one
                    (hmeas_fin h' c (hc_meas h') (hc_meas c))
            _ = ENNReal.ofReal (2 * Real.exp (-2 * ↑m * ε' ^ 2)) := by
                rw [← two_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat]
        calc μ Bad
            ≤ μ Bad' := MeasureTheory.measure_mono hBad_sub_Bad'
          _ ≤ μ (⋃ h ∈ Cf, { xs | |TrueErrorReal X h c D -
                EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
                  (zeroOneLoss Bool)| ≥ ε' }) :=
              MeasureTheory.measure_mono hBad'_sub
          _ ≤ ∑ h ∈ Cf, μ { xs | |TrueErrorReal X h c D -
                EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
                  (zeroOneLoss Bool)| ≥ ε' } :=
              MeasureTheory.measure_biUnion_finset_le _ _
          _ ≤ ∑ _h ∈ Cf, ENNReal.ofReal (2 * Real.exp (-2 * ↑m * ε' ^ 2)) :=
              Finset.sum_le_sum hper_hyp
          _ = ↑N * ENNReal.ofReal (2 * Real.exp (-2 * ↑m * ε' ^ 2)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ENNReal.ofReal (↑N * (2 * Real.exp (-2 * ↑m * ε' ^ 2))) := by
              rw [ENNReal.ofReal_mul (Nat.cast_nonneg' N),
                  ENNReal.ofReal_natCast]
          _ ≤ ENNReal.ofReal δ := by
              apply ENNReal.ofReal_le_ofReal
              by_cases hN_zero : N = 0
              · simp [hN_zero]; linarith
              · have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN_zero)
                have h2N_pos : (0 : ℝ) < 2 * N := by positivity
                have hm_ge : (Real.log (2 * ↑N / δ)) / (2 * ε' ^ 2) ≤ ↑m :=
                  (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 _).trans hm)
                have h2ε2_pos : (0 : ℝ) < 2 * ε' ^ 2 := by positivity
                have hlog_le : Real.log (2 * ↑N / δ) ≤ ↑m * (2 * ε' ^ 2) :=
                  (div_le_iff₀ h2ε2_pos).mp hm_ge
                have hexp_bound : Real.exp (-2 * ↑m * ε' ^ 2) ≤ δ / (2 * ↑N) := by
                  rw [show -2 * ↑m * ε' ^ 2 = -(↑m * (2 * ε' ^ 2)) from by ring]
                  calc Real.exp (-(↑m * (2 * ε' ^ 2)))
                      ≤ Real.exp (-Real.log (2 * ↑N / δ)) :=
                        Real.exp_le_exp_of_le (by linarith)
                    _ = (2 * ↑N / δ)⁻¹ := by
                        rw [Real.exp_neg, Real.exp_log (div_pos h2N_pos hδ)]
                    _ = δ / (2 * ↑N) := by rw [inv_div]
                calc ↑N * (2 * Real.exp (-2 * ↑m * ε' ^ 2))
                    ≤ ↑N * (2 * (δ / (2 * ↑N))) := by gcongr
                    _ = δ := by field_simp [ne_of_gt hN_pos]
      rw [uniform_good_event_eq_bad_compl (D := D) (C := C) (c := c) (m := m) (ε := ε)]
      change ENNReal.ofReal (1 - δ) ≤ μ Badᶜ
      exact bad_event_compl_measure_ge μ Bad hδ h_ub
  · -- ═══ INFINITE X BRANCH ═══
    rw [WithTop.lt_top_iff_ne_top] at hC
    obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hC
    intro ε δ hε hδ
    have hC' : VCDim X C < ⊤ := by
      rw [WithTop.lt_top_iff_ne_top]; exact WithTop.ne_top_iff_exists.mpr ⟨d, hd⟩
    obtain ⟨v₀, hv₀⟩ := vcdim_finite_imp_growth_bounded X C hC'
    set v := max v₀ 1 with hv_def
    have hv_pos : 0 < v := by simp [hv_def]
    have hv₀_le_v : v₀ ≤ v := le_max_left v₀ 1
    have hv : ∀ (n : ℕ), v ≤ n →
        GrowthFunction X C n ≤ ∑ i ∈ Finset.range (v + 1), Nat.choose n i := by
      intro n hn
      have hn₀ : v₀ ≤ n := le_trans hv₀_le_v hn
      calc GrowthFunction X C n
          ≤ ∑ i ∈ Finset.range (v₀ + 1), Nat.choose n i := hv₀ n hn₀
        _ ≤ ∑ i ∈ Finset.range (v + 1), Nat.choose n i := by
            apply Finset.sum_le_sum_of_subset
            apply Finset.range_mono
            omega
    use Nat.ceil ((16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) / δ)
    intro D hD c m hm
    by_cases hδ1 : 1 ≤ δ
    · have : ENNReal.ofReal (1 - δ) = 0 := ENNReal.ofReal_eq_zero.mpr (by linarith)
      rw [this]; exact zero_le
    · push Not at hδ1
      have hm_pos : 0 < m := by
        have h1 : (0 : ℝ) < (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) / δ :=
          div_pos (pow_pos (div_pos (by positivity) (pow_pos hε 2)) (v + 1)) hδ
        exact Nat.lt_of_lt_of_le (Nat.lt_ceil.mpr (by simpa using h1)) hm
      have hE_nullmeas := hWB D c m ε
      have h_ub := uc_bad_event_le_delta_proved D C c hmeas_C (hc_meas c) m hm_pos ε δ hε hδ hδ1
        v hv_pos hv (le_trans (Nat.le_ceil _) (by exact_mod_cast hm)) hE_nullmeas
      set μ := MeasureTheory.Measure.pi (fun _ : Fin m => D)
      set Bad := { xs : Fin m → X | ∃ h ∈ C,
          |TrueErrorReal X h c D -
           EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
             (zeroOneLoss Bool)| ≥ ε }
      rw [uniform_good_event_eq_bad_compl (D := D) (C := C) (c := c) (m := m) (ε := ε)]
      change ENNReal.ofReal (1 - δ) ≤ μ Badᶜ
      exact bad_event_compl_measure_ge μ Bad hδ h_ub
