-- Prove2me | solution 1 for PalmQueueing.Recurrence.growth_rates
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:01:39.315192+00:00
-- url     : https://prove2.me/submissions/a515241f-1165-429a-8ef1-9b64330e540a

import Mathlib
import Definitions.Def_PalmQueueing_Recurrence_MonotoneHomogeneous

open MeasureTheory Filter Topology PalmQueueing.Recurrence

section Kingman

variable {Ω : Type*}

private lemma subadditive_le_birkhoffSum_one {T : Ω → Ω} {g : ℕ → Ω → ℝ}
    (hg0 : ∀ ω, g 0 ω = 0)
    (hsub : ∀ m n ω, g (m + n) ω ≤ g m ω + g n (T^[m] ω)) :
    ∀ n ω, g n ω ≤ birkhoffSum T (g 1) n ω := by
  intro n
  induction n with
  | zero => intro ω; simp [hg0, birkhoffSum]
  | succ n ih =>
    intro ω
    have h1 := hsub n 1 ω
    have h2 := ih ω
    rw [birkhoffSum_succ]
    linarith

private lemma subadditive_mul_le {T : Ω → Ω} {g : ℕ → Ω → ℝ}
    (hg0 : ∀ ω, g 0 ω = 0)
    (hsub : ∀ m n ω, g (m + n) ω ≤ g m ω + g n (T^[m] ω)) :
    ∀ m q ω, g (q * m) ω ≤ ∑ j ∈ Finset.range q, g m (T^[j * m] ω) := by
  intro m q
  induction q with
  | zero => intro ω; simp [hg0]
  | succ q ih =>
    intro ω
    rw [Nat.succ_mul, Finset.sum_range_succ]
    have h1 := hsub (q * m) m ω
    have h2 := ih ω
    linarith

/-- Strong-induction covering bound (Steele's proof of Kingman's theorem). -/
private lemma subadditive_covering_bound {T : Ω → Ω} {g : ℕ → Ω → ℝ}
    (hg0 : ∀ ω, g 0 ω = 0)
    (hsub : ∀ m n ω, g (m + n) ω ≤ g m ω + g n (T^[m] ω))
    (c : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    let A : Set Ω := {ω | ∃ k, 1 ≤ k ∧ k ≤ M ∧ g k ω < c * (k : ℝ)}
    let φ : Ω → ℝ := fun ω => max (g 1 ω - c) 0
    let ψ : Ω → ℝ := fun ω => c + Aᶜ.indicator φ ω
    ∀ N ω, g N ω ≤ (∑ i ∈ Finset.range N, ψ (T^[i] ω)) +
      (∑ i ∈ Finset.Ico (N - M) N, φ (T^[i] ω)) := by
  intro A φ ψ N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro ω
    have hφ_nonneg : ∀ x, 0 ≤ φ x := fun x => le_max_right _ _
    have hc_le_ψ : ∀ x, c ≤ ψ x := fun x => by
      dsimp only [ψ]
      have : 0 ≤ Aᶜ.indicator φ x := Set.indicator_nonneg (fun y _ => hφ_nonneg y) x
      linarith
    have hg1_le : ∀ x, g 1 x ≤ ψ x + φ x := fun x => by
      have h1 : g 1 x ≤ c + φ x := by dsimp only [φ]; linarith [le_max_left (g 1 x - c) 0]
      linarith [hc_le_ψ x]
    by_cases hNM : N < M
    · have hsub0 : N - M = 0 := Nat.sub_eq_zero_of_le (le_of_lt hNM)
      rw [hsub0, Nat.Ico_zero_eq_range, ← Finset.sum_add_distrib]
      calc g N ω ≤ birkhoffSum T (g 1) N ω := subadditive_le_birkhoffSum_one hg0 hsub N ω
        _ = ∑ i ∈ Finset.range N, g 1 (T^[i] ω) := rfl
        _ ≤ ∑ i ∈ Finset.range N, (ψ (T^[i] ω) + φ (T^[i] ω)) :=
            Finset.sum_le_sum (fun i _ => hg1_le _)
    · push Not at hNM
      have step : ∀ k : ℕ, 1 ≤ k → k ≤ M → g k ω ≤ ∑ j ∈ Finset.range k, ψ (T^[j] ω) →
          g N ω ≤ (∑ i ∈ Finset.range N, ψ (T^[i] ω)) +
            (∑ i ∈ Finset.Ico (N - M) N, φ (T^[i] ω)) := by
        intro k hk1 hkM hgk
        have hkN : k ≤ N := le_trans hkM hNM
        have hlt : N - k < N := Nat.sub_lt (by omega) (by omega)
        have h1 := hsub k (N - k) ω
        rw [Nat.add_sub_of_le hkN] at h1
        have h2 := ih (N - k) hlt (T^[k] ω)
        have hsum_ψ :
            (∑ j ∈ Finset.range k, ψ (T^[j] ω)) +
            (∑ i ∈ Finset.range (N - k), ψ (T^[i] (T^[k] ω))) =
            ∑ i ∈ Finset.range N, ψ (T^[i] ω) := by
          have hshift :
              ∑ i ∈ Finset.range (N - k), ψ (T^[i] (T^[k] ω)) =
              ∑ j ∈ Finset.Ico k N, ψ (T^[j] ω) := by
            refine Finset.sum_nbij (· + k) ?_ ?_ ?_ ?_
            · intro i hi
              simp only [Finset.mem_range] at hi
              simp only [Finset.mem_Ico]; omega
            · intro i₁ _ i₂ _ h; dsimp only at h; omega
            · intro j hj
              simp only [Finset.mem_coe, Finset.mem_Ico] at hj
              refine ⟨j - k, ?_, by dsimp only; omega⟩
              simp only [Finset.mem_coe, Finset.mem_range]; omega
            · intro i _
              rw [← Function.iterate_add_apply]
          rw [hshift, Finset.sum_range_add_sum_Ico _ hkN]
        have hsum_φ :
            ∑ i ∈ Finset.Ico ((N - k) - M) (N - k), φ (T^[i] (T^[k] ω)) ≤
            ∑ i ∈ Finset.Ico (N - M) N, φ (T^[i] ω) := by
          have hshift :
              ∑ i ∈ Finset.Ico ((N - k) - M) (N - k), φ (T^[i] (T^[k] ω)) =
              ∑ j ∈ Finset.Ico (((N - k) - M) + k) N, φ (T^[j] ω) := by
            refine Finset.sum_nbij (· + k) ?_ ?_ ?_ ?_
            · intro i hi
              simp only [Finset.mem_Ico] at hi ⊢; omega
            · intro i₁ _ i₂ _ h; dsimp only at h; omega
            · intro j hj
              simp only [Finset.mem_coe, Finset.mem_Ico] at hj
              refine ⟨j - k, ?_, by dsimp only; omega⟩
              simp only [Finset.mem_coe, Finset.mem_Ico]; omega
            · intro i _
              rw [← Function.iterate_add_apply]
          rw [hshift]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hφ_nonneg _)
          intro j hj
          simp only [Finset.mem_Ico] at hj ⊢
          omega
        linarith
      by_cases hA : ω ∈ A
      · rcases hA with ⟨k, hk1, hkM, hgk⟩
        apply step k hk1 hkM
        calc g k ω ≤ c * (k : ℝ) := le_of_lt hgk
          _ = ∑ _j ∈ Finset.range k, c := by simp [mul_comm]
          _ ≤ ∑ j ∈ Finset.range k, ψ (T^[j] ω) := Finset.sum_le_sum (fun j _ => hc_le_ψ _)
      · apply step 1 le_rfl hM
        simp only [Finset.range_one, Finset.sum_singleton, Function.iterate_zero, id_eq]
        dsimp only [ψ]
        rw [Set.indicator_of_mem hA]
        dsimp only [φ]
        linarith [le_max_left (g 1 ω - c) 0]

private lemma measurableEmbedding_iterate_equiv [MeasurableSpace Ω] (θ : Ω ≃ᵐ Ω) (i : ℕ) :
    MeasurableEmbedding ((θ : Ω → Ω)^[i]) := by
  induction i with
  | zero => simpa using MeasurableEmbedding.id
  | succ i ih =>
    rw [Function.iterate_succ']
    exact θ.measurableEmbedding.comp ih

private lemma integrable_comp_iterate_equiv [MeasurableSpace Ω]
    {μ : Measure Ω} {θ : Ω ≃ᵐ Ω} (hθ : MeasurePreserving θ μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (i : ℕ) :
    Integrable (fun ω => f ((θ : Ω → Ω)^[i] ω)) μ :=
  ((hθ.iterate i).integrable_comp_emb (measurableEmbedding_iterate_equiv θ i)).mpr hf

private lemma integral_comp_iterate_equiv [MeasurableSpace Ω]
    {μ : Measure Ω} {θ : Ω ≃ᵐ Ω} (hθ : MeasurePreserving θ μ μ)
    (f : Ω → ℝ) (i : ℕ) :
    ∫ ω, f ((θ : Ω → Ω)^[i] ω) ∂μ = ∫ ω, f ω ∂μ :=
  (hθ.iterate i).integral_comp (measurableEmbedding_iterate_equiv θ i) f

/-- Lower bound half of Kingman's subadditive ergodic theorem. -/
private lemma kingman_liminf_ge [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (θ : Ω ≃ᵐ Ω) (hT : Ergodic θ μ)
    (g : ℕ → Ω → ℝ)
    (hg0 : ∀ ω, g 0 ω = 0)
    (hsub : ∀ m n ω, g (m + n) ω ≤ g m ω + g n ((θ : Ω → Ω)^[m] ω))
    (hint : ∀ n, Integrable (g n) μ)
    (γ : ℝ)
    (hγ : Tendsto (fun n : ℕ => (∫ ω, g n ω ∂μ) / (n : ℝ)) atTop (𝓝 γ)) :
    ∀ᵐ ω ∂μ, ∀ q : ℚ, (q : ℝ) < γ → ∀ᶠ n : ℕ in atTop, (q : ℝ) ≤ g n ω / (n : ℝ) := by
  have hT_mp : MeasurePreserving θ μ μ := hT.toMeasurePreserving
  have h_each : ∀ q : ℚ, (q : ℝ) < γ →
      ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, (q : ℝ) ≤ g n ω / (n : ℝ) := by
    intro q hq
    let F : Set Ω := {ω | ∀ k : ℕ, ∃ᶠ n : ℕ in atTop, g n ω / (n : ℝ) < (q : ℝ) + 1 / ((k : ℝ) + 1)}
    have hF_nm : NullMeasurableSet F μ := by
      have hF_eq : F = ⋂ k : ℕ, ⋂ N : ℕ, ⋃ n ∈ Set.Ici N,
          {ω | g n ω / (n : ℝ) < (q : ℝ) + 1 / ((k : ℝ) + 1)} := by
        ext ω
        simp only [F, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion,
          Filter.frequently_atTop, Set.mem_Ici, exists_prop]
      rw [hF_eq]
      refine NullMeasurableSet.iInter (fun k => NullMeasurableSet.iInter (fun N => ?_))
      refine NullMeasurableSet.iUnion (fun n => NullMeasurableSet.iUnion (fun _ => ?_))
      have hm : AEMeasurable (fun ω => g n ω / (n : ℝ)) μ :=
        (hint n).aemeasurable.div_const (n : ℝ)
      exact hm.nullMeasurable measurableSet_Iio
    have hF_inv : θ ⁻¹' F ⊆ F := by
      intro ω hω k
      have hk' := hω (2 * k + 1)
      have hlt : (q : ℝ) + 1 / (((2 * k + 1 : ℕ) : ℝ) + 1) < (q : ℝ) + 1 / ((k : ℝ) + 1) := by
        have hpos1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have hlt' : (k : ℝ) + 1 < ((2 * k + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
        linarith [one_div_lt_one_div_of_lt hpos1 hlt']
      have h_tend : Tendsto
          (fun n : ℕ => g 1 ω / ((n + 1 : ℕ) : ℝ) +
            ((q : ℝ) + 1 / (((2 * k + 1 : ℕ) : ℝ) + 1)) * ((n : ℝ) / ((n + 1 : ℕ) : ℝ)))
          atTop (𝓝 (0 + ((q : ℝ) + 1 / (((2 * k + 1 : ℕ) : ℝ) + 1)) * 1)) := by
        refine Tendsto.add ?_ (Tendsto.mul tendsto_const_nhds ?_)
        · exact tendsto_const_nhds.div_atTop
            (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
        · have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (1 + 1 / (n : ℝ))) atTop (𝓝 (1 / (1 + 0))) :=
            tendsto_const_nhds.div
              (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop))
              (by norm_num)
          rw [add_zero, div_one] at h1
          refine h1.congr' ?_
          filter_upwards [eventually_ge_atTop 1] with n hn
          have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          push_cast
          field_simp
      rw [zero_add, mul_one] at h_tend
      have hev : ∀ᶠ n : ℕ in atTop,
          g 1 ω / ((n + 1 : ℕ) : ℝ) +
            ((q : ℝ) + 1 / (((2 * k + 1 : ℕ) : ℝ) + 1)) * ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) <
          (q : ℝ) + 1 / ((k : ℝ) + 1) :=
        h_tend.eventually (gt_mem_nhds hlt)
      have hfreq : ∃ᶠ n : ℕ in atTop,
          g (n + 1) ω / ((n + 1 : ℕ) : ℝ) < (q : ℝ) + 1 / ((k : ℝ) + 1) := by
        refine (hk'.and_eventually (hev.and (eventually_ge_atTop 1))).mono ?_
        rintro n ⟨hgn, hbound, hn1⟩
        have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
        have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        have hsub1 : g (n + 1) ω ≤ g 1 ω + g n (θ ω) := by
          simpa [Nat.add_comm] using hsub 1 n ω
        have hgn' : g n (θ ω) < ((q : ℝ) + 1 / (((2 * k + 1 : ℕ) : ℝ) + 1)) * (n : ℝ) :=
          (div_lt_iff₀ hn_pos).mp hgn
        calc g (n + 1) ω / ((n + 1 : ℕ) : ℝ)
            ≤ (g 1 ω + g n (θ ω)) / ((n + 1 : ℕ) : ℝ) :=
              div_le_div_of_nonneg_right hsub1 (le_of_lt hn1_pos)
          _ < (g 1 ω + ((q : ℝ) + 1 / (((2 * k + 1 : ℕ) : ℝ) + 1)) * (n : ℝ)) /
                ((n + 1 : ℕ) : ℝ) :=
              div_lt_div_of_pos_right (by linarith) hn1_pos
          _ = g 1 ω / ((n + 1 : ℕ) : ℝ) +
                ((q : ℝ) + 1 / (((2 * k + 1 : ℕ) : ℝ) + 1)) * ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
              ring
          _ < (q : ℝ) + 1 / ((k : ℝ) + 1) := hbound
      rw [Filter.frequently_atTop] at hfreq ⊢
      intro N
      obtain ⟨n, hn, hlt'⟩ := hfreq N
      exact ⟨n + 1, by omega, hlt'⟩
    have h01 := hT.ae_empty_or_univ_of_preimage_ae_le hF_nm (LE.le.eventuallyLE hF_inv)
    have hF_null : F =ᵐ[μ] (∅ : Set Ω) := by
      rcases h01 with h0 | h1
      · exact h0
      · exfalso
        set c' : ℝ := ((q : ℝ) + γ) / 2
        have hq_lt_c' : (q : ℝ) < c' := by dsimp only [c']; linarith
        have hc'_lt_γ : c' < γ := by dsimp only [c']; linarith
        let A : ℕ → Set Ω := fun M => {ω | ∃ k, 1 ≤ k ∧ k ≤ M ∧ g k ω < c' * (k : ℝ)}
        let φ : Ω → ℝ := fun ω => max (g 1 ω - c') 0
        have hφ_int : Integrable φ μ := ((hint 1).sub (integrable_const c')).sup (integrable_const 0)
        have hφ_nonneg : ∀ ω, 0 ≤ φ ω := fun ω => le_max_right _ _
        have hA_nm : ∀ M, NullMeasurableSet (A M) μ := by
          intro M
          have hA_eq : A M = ⋃ k ∈ Finset.Icc 1 M, {ω | g k ω < c' * (k : ℝ)} := by
            ext ω; simp [A, and_assoc]
          rw [hA_eq]
          refine NullMeasurableSet.iUnion (fun k => NullMeasurableSet.iUnion (fun _ => ?_))
          exact (hint k).aemeasurable.nullMeasurable measurableSet_Iio
        have h_le_M : ∀ M : ℕ, 1 ≤ M → γ ≤ c' + ∫ ω, (A M)ᶜ.indicator φ ω ∂μ := by
          intro M hM
          obtain ⟨t, _, ht_meas, ht_ae⟩ := (hA_nm M).exists_measurable_subset_ae_eq
          have hind_ae : (A M)ᶜ.indicator φ =ᵐ[μ] tᶜ.indicator φ := by
            filter_upwards [ht_ae] with ω hω
            have hiff : ω ∈ (A M)ᶜ ↔ ω ∈ tᶜ := by
              change ¬ A M ω ↔ ¬ t ω
              rw [hω]
            by_cases h : ω ∈ tᶜ
            · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mpr h)]
            · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hiff.mp h)]
          have hind_int : Integrable ((A M)ᶜ.indicator φ) μ :=
            (hφ_int.indicator ht_meas.compl).congr hind_ae.symm
          let ψ : Ω → ℝ := fun ω => c' + (A M)ᶜ.indicator φ ω
          have hψ_int : Integrable ψ μ := (integrable_const c').add hind_int
          have h_bound : ∀ N : ℕ, 1 ≤ N →
              (∫ ω, g N ω ∂μ) / (N : ℝ) ≤
                (∫ ω, ψ ω ∂μ) + ((M : ℝ) / (N : ℝ)) * (∫ ω, φ ω ∂μ) := by
            intro N hN
            have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
            have hcov := subadditive_covering_bound hg0 hsub c' M hM N
            have hψ_sum_int : Integrable (fun ω => ∑ i ∈ Finset.range N, ψ ((θ : Ω → Ω)^[i] ω)) μ :=
              integrable_finsetSum _ (fun i _ => integrable_comp_iterate_equiv hT_mp hψ_int i)
            have hφ_sum_int : Integrable (fun ω => ∑ i ∈ Finset.Ico (N - M) N, φ ((θ : Ω → Ω)^[i] ω)) μ :=
              integrable_finsetSum _ (fun i _ => integrable_comp_iterate_equiv hT_mp hφ_int i)
            have hint_le : ∫ ω, g N ω ∂μ ≤
                ∫ ω, ((∑ i ∈ Finset.range N, ψ ((θ : Ω → Ω)^[i] ω)) +
                  (∑ i ∈ Finset.Ico (N - M) N, φ ((θ : Ω → Ω)^[i] ω))) ∂μ :=
              integral_mono (hint N) (hψ_sum_int.add hφ_sum_int) hcov
            rw [integral_add hψ_sum_int hφ_sum_int,
              integral_finsetSum _ (fun i _ => integrable_comp_iterate_equiv hT_mp hψ_int i),
              integral_finsetSum _ (fun i _ => integrable_comp_iterate_equiv hT_mp hφ_int i)]
              at hint_le
            have h1 : ∑ i ∈ Finset.range N, ∫ ω, ψ ((θ : Ω → Ω)^[i] ω) ∂μ = (N : ℝ) * ∫ ω, ψ ω ∂μ := by
              simp only [integral_comp_iterate_equiv hT_mp ψ, Finset.sum_const, Finset.card_range,
                nsmul_eq_mul]
            have h2 : ∑ i ∈ Finset.Ico (N - M) N, ∫ ω, φ ((θ : Ω → Ω)^[i] ω) ∂μ ≤
                (M : ℝ) * ∫ ω, φ ω ∂μ := by
              simp only [integral_comp_iterate_equiv hT_mp φ, Finset.sum_const, Nat.card_Ico,
                nsmul_eq_mul]
              have hcard : ((N - (N - M) : ℕ) : ℝ) ≤ (M : ℝ) := by
                exact_mod_cast (by omega : N - (N - M) ≤ M)
              exact mul_le_mul_of_nonneg_right hcard (integral_nonneg hφ_nonneg)
            rw [h1] at hint_le
            have h3 : ∫ ω, g N ω ∂μ ≤ (N : ℝ) * ∫ ω, ψ ω ∂μ + (M : ℝ) * ∫ ω, φ ω ∂μ := by
              linarith
            rw [div_le_iff₀ hN_pos]
            calc ∫ ω, g N ω ∂μ ≤ (N : ℝ) * ∫ ω, ψ ω ∂μ + (M : ℝ) * ∫ ω, φ ω ∂μ := h3
              _ = ((∫ ω, ψ ω ∂μ) + (M : ℝ) / (N : ℝ) * ∫ ω, φ ω ∂μ) * (N : ℝ) := by
                  field_simp
          have h_rhs_tend : Tendsto
              (fun N : ℕ => (∫ ω, ψ ω ∂μ) + ((M : ℝ) / (N : ℝ)) * (∫ ω, φ ω ∂μ))
              atTop (𝓝 ((∫ ω, ψ ω ∂μ) + 0 * (∫ ω, φ ω ∂μ))) :=
            tendsto_const_nhds.add
              ((tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).mul tendsto_const_nhds)
          rw [zero_mul, add_zero] at h_rhs_tend
          have hγ_le_ψ : γ ≤ ∫ ω, ψ ω ∂μ :=
            le_of_tendsto_of_tendsto hγ h_rhs_tend (by
              filter_upwards [eventually_ge_atTop 1] with N hN
              exact h_bound N hN)
          have hψ_eq : ∫ ω, ψ ω ∂μ = c' + ∫ ω, (A M)ᶜ.indicator φ ω ∂μ := by
            dsimp only [ψ]
            rw [integral_add (integrable_const c') hind_int, integral_const, probReal_univ, one_smul]
          linarith
        have h_ae_zero : ∀ᵐ ω ∂μ, Tendsto (fun M : ℕ => (A M)ᶜ.indicator φ ω) atTop (𝓝 0) := by
          filter_upwards [ae_eq_univ.mp h1] with ω hω
          obtain ⟨k, hk⟩ : ∃ k : ℕ, (q : ℝ) + 1 / ((k : ℝ) + 1) ≤ c' := by
            obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hq_lt_c')
            exact ⟨k, by linarith⟩
          have hfreq := hω k
          rw [Filter.frequently_atTop] at hfreq
          obtain ⟨n, hn1, hlt⟩ := hfreq 1
          have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
          have hgn : g n ω < c' * (n : ℝ) := (div_lt_iff₀ hn_pos).mp (lt_of_lt_of_le hlt hk)
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [eventually_ge_atTop n] with M hM
          have hmem : ω ∈ A M := ⟨n, hn1, hM, hgn⟩
          rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hmem)]
        have h_int_tend : Tendsto (fun M : ℕ => ∫ ω, (A M)ᶜ.indicator φ ω ∂μ) atTop (𝓝 0) := by
          have h_zero : (0 : ℝ) = ∫ _ω, (0 : ℝ) ∂μ := by simp
          rw [h_zero]
          refine tendsto_integral_of_dominated_convergence φ ?_ hφ_int ?_ h_ae_zero
          · intro M
            obtain ⟨t, _, ht_meas, ht_ae⟩ := (hA_nm M).exists_measurable_subset_ae_eq
            have hind_ae : (A M)ᶜ.indicator φ =ᵐ[μ] tᶜ.indicator φ := by
              filter_upwards [ht_ae] with ω hω
              have hiff : ω ∈ (A M)ᶜ ↔ ω ∈ tᶜ := by
                change ¬ A M ω ↔ ¬ t ω
                rw [hω]
              by_cases h : ω ∈ tᶜ
              · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mpr h)]
              · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hiff.mp h)]
            exact (hφ_int.aestronglyMeasurable.indicator ht_meas.compl).congr hind_ae.symm
          · intro M
            refine Eventually.of_forall (fun ω => ?_)
            rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun y _ => hφ_nonneg y) ω)]
            exact Set.indicator_le_self' (fun y _ => hφ_nonneg y) ω
        have hγ_le_c' : γ ≤ c' := by
          have h_tend2 : Tendsto (fun M : ℕ => c' + ∫ ω, (A M)ᶜ.indicator φ ω ∂μ) atTop (𝓝 (c' + 0)) :=
            tendsto_const_nhds.add h_int_tend
          rw [add_zero] at h_tend2
          exact ge_of_tendsto h_tend2 (by
            filter_upwards [eventually_ge_atTop 1] with M hM
            exact h_le_M M hM)
        linarith
    have hF_ae_not : ∀ᵐ ω ∂μ, ω ∉ F := by
      filter_upwards [hF_null] with ω hω
      intro hmem
      have : ω ∈ (∅ : Set Ω) := by change (∅ : Set Ω) ω; rw [← hω]; exact hmem
      exact this
    filter_upwards [hF_ae_not] with ω hω
    simp only [F, Set.mem_ofPred_eq, not_forall, Filter.not_frequently, not_lt] at hω
    obtain ⟨k, hk⟩ := hω
    refine hk.mono (fun n hn => ?_)
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  rw [ae_all_iff]
  intro q
  by_cases hq : (q : ℝ) < γ
  · filter_upwards [h_each q hq] with ω hω _ using hω
  · exact Eventually.of_forall (fun _ h => absurd h hq)

/-- Helper: combining rational lower and upper bounds yields convergence in `ℝ`. -/
private lemma tendsto_of_rat_bounds {u : ℕ → ℝ} {L : ℝ}
    (hlow : ∀ q : ℚ, (q : ℝ) < L → ∀ᶠ n : ℕ in atTop, (q : ℝ) ≤ u n)
    (hup : ∀ q : ℚ, L < (q : ℝ) → ∀ᶠ n : ℕ in atTop, u n ≤ (q : ℝ)) :
    Tendsto u atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨q1, hq1_lt, hq1_gt⟩ := exists_rat_btwn (sub_lt_self L hε)
  obtain ⟨q2, hq2_gt, hq2_lt⟩ := exists_rat_btwn (lt_add_of_pos_right L hε)
  have hev := (hlow q1 hq1_gt).and (hup q2 hq2_gt)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Birkhoff's ergodic theorem as an immediate corollary of `kingman_liminf_ge`. -/
private lemma birkhoff_ergodic_ae [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (θ : Ω ≃ᵐ Ω) (hT : Ergodic θ μ)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => birkhoffSum (θ : Ω → Ω) f n ω / (n : ℝ))
      atTop (𝓝 (∫ ω, f ω ∂μ)) := by
  have hT_mp : MeasurePreserving θ μ μ := hT.toMeasurePreserving
  have h_half : ∀ (f' : Ω → ℝ), Integrable f' μ →
      ∀ᵐ ω ∂μ, ∀ q : ℚ, (q : ℝ) < ∫ ω, f' ω ∂μ →
        ∀ᶠ n : ℕ in atTop, (q : ℝ) ≤ birkhoffSum (θ : Ω → Ω) f' n ω / (n : ℝ) := by
    intro f' hf'
    refine kingman_liminf_ge μ θ hT (fun n ω => birkhoffSum (θ : Ω → Ω) f' n ω)
      (fun ω => birkhoffSum_zero _ _ ω)
      (fun m n ω => le_of_eq (birkhoffSum_add _ _ m n ω))
      (fun n => integrable_finsetSum _ (fun i _ => integrable_comp_iterate_equiv hT_mp hf' i))
      (∫ ω, f' ω ∂μ) ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    dsimp only [birkhoffSum]
    rw [integral_finsetSum _ (fun i _ => integrable_comp_iterate_equiv hT_mp hf' i)]
    simp only [integral_comp_iterate_equiv hT_mp f', Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    field_simp
  filter_upwards [h_half f hf, h_half (-f) hf.neg] with ω hlow hup
  refine tendsto_of_rat_bounds hlow ?_
  intro q hq
  have hq' : ((-q : ℚ) : ℝ) < ∫ ω, (-f) ω ∂μ := by
    simp only [Pi.neg_apply, integral_neg]
    push_cast
    linarith
  filter_upwards [hup (-q) hq'] with n hn
  rw [birkhoffSum_neg, neg_div] at hn
  push_cast at hn
  linarith

/-- Averaging identity for `m`-strided Birkhoff sums. -/
private lemma sum_stride_birkhoff {α : Type*} [AddCommMonoid α] (F : ℕ → α)
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∑ s ∈ Finset.range m, ∑ j ∈ Finset.range ((n - s) / m), F (s + j * m) =
    ∑ k ∈ Finset.range (n - m + 1), F k := by
  have hsig : ∑ s ∈ Finset.range m, ∑ j ∈ Finset.range ((n - s) / m), F (s + j * m) =
      ∑ p ∈ (Finset.range m).sigma (fun s => Finset.range ((n - s) / m)), F (p.1 + p.2 * m) :=
    (Finset.sum_sigma (Finset.range m) (fun s => Finset.range ((n - s) / m))
      (fun p => F (p.1 + p.2 * m))).symm
  rw [hsig]
  refine Finset.sum_nbij (fun p : Σ _ : ℕ, ℕ => p.1 + p.2 * m) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    simp only [Finset.mem_range]
    have h1 : (p.2 + 1) * m ≤ n - p.1 := by
      have := (Nat.le_div_iff_mul_le (by omega : 0 < m)).mp (Nat.succ_le_of_lt hp.2)
      exact this
    have h2 : p.1 + p.2 * m + m ≤ n := by
      have : p.2 * m + m ≤ n - p.1 := by simpa [Nat.succ_mul] using h1
      omega
    omega
  · intro p₁ hp₁ p₂ hp₂ heq
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range] at hp₁ hp₂
    dsimp only at heq
    have hmod : p₁.1 = p₂.1 := by
      have h1 : (p₁.1 + p₁.2 * m) % m = p₁.1 := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp₁.1]
      have h2 : (p₂.1 + p₂.2 * m) % m = p₂.1 := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp₂.1]
      rw [← h1, heq, h2]
    have hdiv : p₁.2 = p₂.2 := by
      have : p₁.2 * m = p₂.2 * m := by omega
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
    cases p₁; cases p₂; simp_all
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_range] at hk
    refine ⟨⟨k % m, k / m⟩, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range]
      refine ⟨Nat.mod_lt k (by omega), ?_⟩
      have hkm : k % m + (k / m) * m = k := by
        have := Nat.div_add_mod k m
        linarith [mul_comm m (k / m)]
      have hle : (k / m + 1) * m ≤ n - k % m := by
        rw [Nat.succ_mul]; omega
      have := (Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr hle
      omega
    · dsimp only
      have := Nat.div_add_mod k m
      linarith [mul_comm m (k / m)]
  · intro p _; rfl

/-- Kingman's subadditive ergodic theorem (ergodic case). -/
private theorem kingman_subadditive_ergodic [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (θ : Ω ≃ᵐ Ω) (hT : Ergodic θ μ)
    (g : ℕ → Ω → ℝ)
    (hg0 : ∀ ω, g 0 ω = 0)
    (hsub : ∀ m n ω, g (m + n) ω ≤ g m ω + g n ((θ : Ω → Ω)^[m] ω))
    (hint : ∀ n, Integrable (g n) μ)
    (B : ℝ) (hlb : ∀ n : ℕ, -(B * (n : ℝ)) ≤ ∫ ω, g n ω ∂μ) :
    ∃ γ : ℝ,
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => g n ω / (n : ℝ)) atTop (𝓝 γ)) ∧
      Tendsto (fun n : ℕ => (∫ ω, g n ω ∂μ) / (n : ℝ)) atTop (𝓝 γ) := by
  have hT_mp : MeasurePreserving θ μ μ := hT.toMeasurePreserving
  let u : ℕ → ℝ := fun n => ∫ ω, g n ω ∂μ
  have hu_sub : Subadditive u := by
    intro m n
    dsimp only [u]
    have h_int_shift : Integrable (fun ω => g n ((θ : Ω → Ω)^[m] ω)) μ :=
      integrable_comp_iterate_equiv hT_mp (hint n) m
    have hle := integral_mono (hint (m + n)) ((hint m).add h_int_shift) (hsub m n)
    simp only [Pi.add_apply] at hle
    rw [integral_add (hint m) h_int_shift, integral_comp_iterate_equiv hT_mp (g n) m] at hle
    exact hle
  have hu_bdd : BddBelow (Set.range (fun n : ℕ => u n / (n : ℝ))) := by
    refine ⟨min 0 (-B), ?_⟩
    rintro _ ⟨n, rfl⟩
    by_cases hn : n = 0
    · subst hn; simp
    · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have h1 : -B ≤ u n / (n : ℝ) := by
        rw [le_div_iff₀ hn_pos]
        have := hlb n
        dsimp only [u]
        linarith
      exact le_trans (min_le_right _ _) h1
  set γ : ℝ := hu_sub.lim
  have hγ : Tendsto (fun n : ℕ => u n / (n : ℝ)) atTop (𝓝 γ) := hu_sub.tendsto_lim hu_bdd
  refine ⟨γ, ?_, hγ⟩
  have hlow := kingman_liminf_ge μ θ hT g hg0 hsub hint γ hγ
  -- Upper bound via m-averaging + Birkhoff's ergodic theorem
  let φ : Ω → ℝ := fun ω => max (g 1 ω) 0
  have hφ_int : Integrable φ μ := (hint 1).sup (integrable_const 0)
  have hφ_nonneg : ∀ ω, 0 ≤ φ ω := fun ω => le_max_right _ _
  have h_birk_φ := birkhoff_ergodic_ae μ θ hT φ hφ_int
  have h_up_m : ∀ m : ℕ, 1 ≤ m →
      ∀ᵐ ω ∂μ, ∀ q : ℚ, u m / (m : ℝ) < (q : ℝ) →
        ∀ᶠ n : ℕ in atTop, g n ω / (n : ℝ) ≤ (q : ℝ) := by
    intro m hm
    have h_birk_m := birkhoff_ergodic_ae μ θ hT (g m) (hint m)
    filter_upwards [h_birk_m, h_birk_φ] with ω hbm hbφ q hq
    -- For n ≥ m, m * g n ω ≤ C_ω + birkhoffSum θ (g m) (n - m + 1) ω + m * (S_φ n - S_φ (n - m))
    have h_ineq : ∀ n : ℕ, m ≤ n →
        (m : ℝ) * g n ω ≤
          (∑ s ∈ Finset.range m, g s ω) +
          birkhoffSum (θ : Ω → Ω) (g m) (n - m + 1) ω +
          (m : ℝ) * (birkhoffSum (θ : Ω → Ω) φ n ω - birkhoffSum (θ : Ω → Ω) φ (n - m) ω) := by
      intro n hmn
      have h_each_s : ∀ s ∈ Finset.range m,
          g n ω ≤ g s ω +
            (∑ j ∈ Finset.range ((n - s) / m), g m ((θ : Ω → Ω)^[s + j * m] ω)) +
            (birkhoffSum (θ : Ω → Ω) φ n ω - birkhoffSum (θ : Ω → Ω) φ (n - m) ω) := by
        intro s hs
        simp only [Finset.mem_range] at hs
        set qs := (n - s) / m
        set rs := (n - s) % m
        have hdecomp : s + (qs * m + rs) = n := by
          have := Nat.div_add_mod (n - s) m
          have : m * qs + rs = n - s := this
          have : qs * m + rs = n - s := by linarith [mul_comm m qs]
          omega
        have hrs_lt : rs < m := Nat.mod_lt (n - s) (by omega)
        have h1 : g n ω ≤ g s ω + g (qs * m + rs) ((θ : Ω → Ω)^[s] ω) := by
          rw [← hdecomp]; exact hsub s (qs * m + rs) ω
        have h2 : g (qs * m + rs) ((θ : Ω → Ω)^[s] ω) ≤
            g (qs * m) ((θ : Ω → Ω)^[s] ω) + g rs ((θ : Ω → Ω)^[qs * m] ((θ : Ω → Ω)^[s] ω)) :=
          hsub (qs * m) rs _
        have h3 : g (qs * m) ((θ : Ω → Ω)^[s] ω) ≤
            ∑ j ∈ Finset.range qs, g m ((θ : Ω → Ω)^[s + j * m] ω) := by
          calc g (qs * m) ((θ : Ω → Ω)^[s] ω)
              ≤ ∑ j ∈ Finset.range qs, g m ((θ : Ω → Ω)^[j * m] ((θ : Ω → Ω)^[s] ω)) :=
                subadditive_mul_le hg0 hsub m qs _
            _ = ∑ j ∈ Finset.range qs, g m ((θ : Ω → Ω)^[s + j * m] ω) := by
                refine Finset.sum_congr rfl (fun j _ => ?_)
                rw [← Function.iterate_add_apply, Nat.add_comm]
        have h4 : g rs ((θ : Ω → Ω)^[qs * m] ((θ : Ω → Ω)^[s] ω)) ≤
            birkhoffSum (θ : Ω → Ω) φ n ω - birkhoffSum (θ : Ω → Ω) φ (n - m) ω := by
          have h4a := subadditive_le_birkhoffSum_one hg0 hsub rs ((θ : Ω → Ω)^[qs * m] ((θ : Ω → Ω)^[s] ω))
          have h4b : birkhoffSum (θ : Ω → Ω) (g 1) rs ((θ : Ω → Ω)^[qs * m] ((θ : Ω → Ω)^[s] ω)) ≤
              ∑ i ∈ Finset.range rs, φ ((θ : Ω → Ω)^[i + (s + qs * m)] ω) := by
            dsimp only [birkhoffSum]
            refine Finset.sum_le_sum (fun i _ => ?_)
            rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
            have hidx : i + qs * m + s = i + (s + qs * m) := by omega
            rw [hidx]
            exact le_max_left _ _
          have h4c : ∑ i ∈ Finset.range rs, φ ((θ : Ω → Ω)^[i + (s + qs * m)] ω) =
              ∑ k ∈ Finset.Ico (s + qs * m) n, φ ((θ : Ω → Ω)^[k] ω) := by
            refine Finset.sum_nbij (· + (s + qs * m)) ?_ ?_ ?_ ?_
            · intro i hi
              simp only [Finset.mem_range] at hi
              simp only [Finset.mem_Ico]; omega
            · intro i₁ _ i₂ _ h; dsimp only at h; omega
            · intro k hk
              simp only [Finset.mem_coe, Finset.mem_Ico] at hk
              refine ⟨k - (s + qs * m), ?_, by dsimp only; omega⟩
              simp only [Finset.mem_coe, Finset.mem_range]; omega
            · intro i _; rfl
          have h4d : ∑ k ∈ Finset.Ico (s + qs * m) n, φ ((θ : Ω → Ω)^[k] ω) ≤
              ∑ k ∈ Finset.Ico (n - m) n, φ ((θ : Ω → Ω)^[k] ω) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hφ_nonneg _)
            intro k hk
            simp only [Finset.mem_Ico] at hk ⊢
            omega
          have h4e : ∑ k ∈ Finset.Ico (n - m) n, φ ((θ : Ω → Ω)^[k] ω) =
              birkhoffSum (θ : Ω → Ω) φ n ω - birkhoffSum (θ : Ω → Ω) φ (n - m) ω := by
            dsimp only [birkhoffSum]
            have := Finset.sum_range_add_sum_Ico (fun k => φ ((θ : Ω → Ω)^[k] ω)) (Nat.sub_le n m)
            linarith
          linarith
        linarith
      have hsum := Finset.sum_le_sum h_each_s
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib] at hsum
      rw [sum_stride_birkhoff (fun k => g m ((θ : Ω → Ω)^[k] ω)) hm hmn] at hsum
      exact hsum
    -- Now show the RHS divided by (m * n) converges to u m / m < q
    have h_shift_tend : Tendsto (fun n : ℕ => birkhoffSum (θ : Ω → Ω) (g m) (n - m + 1) ω / (n : ℝ))
        atTop (𝓝 (u m)) := by
      have hcomp : Tendsto (fun n : ℕ => birkhoffSum (θ : Ω → Ω) (g m) (n - m + 1) ω / ((n - m + 1 : ℕ) : ℝ))
          atTop (𝓝 (u m)) := by
        refine hbm.comp ?_
        rw [tendsto_atTop_atTop]
        intro b
        exact ⟨b + m, fun n hn => by omega⟩
      have hratio : Tendsto (fun n : ℕ => ((n - m + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
        have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - ((m : ℝ) - 1) / (n : ℝ)) atTop (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
        rw [sub_zero] at h1
        refine h1.congr' ?_
        filter_upwards [eventually_ge_atTop (max m 1)] with n hn
        have hmn : m ≤ n := le_trans (le_max_left _ _) hn
        have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
        have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        rw [Nat.cast_add, Nat.cast_sub hmn, Nat.cast_one]
        field_simp
        ring
      have hmul := hcomp.mul hratio
      rw [mul_one] at hmul
      refine hmul.congr' ?_
      filter_upwards [eventually_ge_atTop (max m 1)] with n hn
      have hmn : m ≤ n := le_trans (le_max_left _ _) hn
      have hpos : ((n - m + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
    have h_tail_tend : Tendsto
        (fun n : ℕ => (birkhoffSum (θ : Ω → Ω) φ n ω - birkhoffSum (θ : Ω → Ω) φ (n - m) ω) / (n : ℝ))
        atTop (𝓝 0) := by
      have hsub_tend : Tendsto (fun n : ℕ => birkhoffSum (θ : Ω → Ω) φ (n - m) ω / (n : ℝ))
          atTop (𝓝 (∫ ω, φ ω ∂μ)) := by
        have hcomp : Tendsto (fun n : ℕ => birkhoffSum (θ : Ω → Ω) φ (n - m) ω / ((n - m : ℕ) : ℝ))
            atTop (𝓝 (∫ ω, φ ω ∂μ)) :=
          hbφ.comp (tendsto_atTop_atTop.mpr (fun b => ⟨b + m, fun n hn => by omega⟩))
        have hratio : Tendsto (fun n : ℕ => ((n - m : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
          have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - (m : ℝ) / (n : ℝ)) atTop (𝓝 (1 - 0)) :=
            tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
          rw [sub_zero] at h1
          refine h1.congr' ?_
          filter_upwards [eventually_ge_atTop (max m 1)] with n hn
          have hmn : m ≤ n := le_trans (le_max_left _ _) hn
          have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
          have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          rw [Nat.cast_sub hmn]
          field_simp
        have hmul := hcomp.mul hratio
        rw [mul_one] at hmul
        refine hmul.congr' ?_
        filter_upwards [eventually_ge_atTop (m + 1)] with n hn
        have hpos : ((n - m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp
      have hdiff := hbφ.sub hsub_tend
      rw [sub_self] at hdiff
      refine hdiff.congr (fun n => by rw [sub_div])
    have h_rhs_tend : Tendsto
        (fun n : ℕ =>
          (∑ s ∈ Finset.range m, g s ω) / ((m : ℝ) * (n : ℝ)) +
          (birkhoffSum (θ : Ω → Ω) (g m) (n - m + 1) ω / (n : ℝ)) / (m : ℝ) +
          (birkhoffSum (θ : Ω → Ω) φ n ω - birkhoffSum (θ : Ω → Ω) φ (n - m) ω) / (n : ℝ))
        atTop (𝓝 (0 + u m / (m : ℝ) + 0)) := by
      refine (Tendsto.add ?_ (h_shift_tend.div_const (m : ℝ))).add h_tail_tend
      have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
      exact tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.const_mul_atTop hm_pos)
    rw [zero_add, add_zero] at h_rhs_tend
    filter_upwards [h_rhs_tend.eventually (gt_mem_nhds hq), eventually_ge_atTop (max m 1)] with n hlt hn
    have hmn : m ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hmn_pos : (0 : ℝ) < (m : ℝ) * (n : ℝ) := mul_pos hm_pos hn_pos
    have h1 := h_ineq n hmn
    have h2 : g n ω / (n : ℝ) ≤
        (∑ s ∈ Finset.range m, g s ω) / ((m : ℝ) * (n : ℝ)) +
        (birkhoffSum (θ : Ω → Ω) (g m) (n - m + 1) ω / (n : ℝ)) / (m : ℝ) +
        (birkhoffSum (θ : Ω → Ω) φ n ω - birkhoffSum (θ : Ω → Ω) φ (n - m) ω) / (n : ℝ) := by
      rw [div_le_iff₀ hn_pos]
      have h3 : (m : ℝ) * g n ω / (m : ℝ) ≤
          ((∑ s ∈ Finset.range m, g s ω) +
          birkhoffSum (θ : Ω → Ω) (g m) (n - m + 1) ω +
          (m : ℝ) * (birkhoffSum (θ : Ω → Ω) φ n ω - birkhoffSum (θ : Ω → Ω) φ (n - m) ω)) / (m : ℝ) :=
        div_le_div_of_nonneg_right h1 (le_of_lt hm_pos)
      rw [mul_div_cancel_left₀ _ (ne_of_gt hm_pos)] at h3
      calc g n ω ≤ ((∑ s ∈ Finset.range m, g s ω) +
            birkhoffSum (θ : Ω → Ω) (g m) (n - m + 1) ω +
            (m : ℝ) * (birkhoffSum (θ : Ω → Ω) φ n ω - birkhoffSum (θ : Ω → Ω) φ (n - m) ω)) / (m : ℝ) := h3
        _ = ((∑ s ∈ Finset.range m, g s ω) / ((m : ℝ) * (n : ℝ)) +
            (birkhoffSum (θ : Ω → Ω) (g m) (n - m + 1) ω / (n : ℝ)) / (m : ℝ) +
            (birkhoffSum (θ : Ω → Ω) φ n ω - birkhoffSum (θ : Ω → Ω) φ (n - m) ω) / (n : ℝ)) * (n : ℝ) := by
            field_simp
    exact le_trans h2 (le_of_lt hlt)
  have hup : ∀ᵐ ω ∂μ, ∀ q : ℚ, γ < (q : ℝ) → ∀ᶠ n : ℕ in atTop, g n ω / (n : ℝ) ≤ (q : ℝ) := by
    rw [ae_all_iff]
    intro q
    by_cases hq : γ < (q : ℝ)
    · have hev := (hγ.eventually (gt_mem_nhds hq)).and (eventually_ge_atTop 1)
      obtain ⟨m, hm_lt, hm1⟩ := hev.exists
      filter_upwards [h_up_m m hm1] with ω hω _
      exact hω q hm_lt
    · exact Eventually.of_forall (fun _ h => absurd h hq)
  filter_upwards [hlow, hup] with ω h1 h2
  exact tendsto_of_rat_bounds h1 h2

end Kingman

section MHRecurrence

variable {Ω : Type*} [MeasurableSpace Ω]

private lemma isNonExpansive_of_mh {K : ℕ} {phi : (Fin K → ℝ) → Fin K → ℝ}
    (hmono : IsMonotoneMap phi) (hhom : IsHomogeneousMap phi) :
    IsNonExpansiveMap phi := by
  intro x y
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))]
  intro i
  set d : ℝ := ‖x - y‖
  have hle : x ≤ y + d • onesVec K := by
    intro j
    have hj : |x j - y j| ≤ d := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (x - y) j
    have := (abs_le.mp hj).2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, onesVec, mul_one]
    linarith
  have hge : y + (-d) • onesVec K ≤ x := by
    intro j
    have hj : |x j - y j| ≤ d := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (x - y) j
    have := (abs_le.mp hj).1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, onesVec, mul_one]
    linarith
  have h1 := hmono x (y + d • onesVec K) hle i
  rw [hhom y d] at h1
  have h2 := hmono (y + (-d) • onesVec K) x hge i
  rw [hhom y (-d)] at h2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, onesVec, mul_one] at h1 h2
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

private lemma measurable_comp_caratheodory {K : ℕ} {F : Type*} [MeasurableSpace F]
    (h : (Fin K → ℝ) → F → Fin K → ℝ)
    (hMH : IsMHRecurrence h)
    (hh : ∀ x : Fin K → ℝ, Measurable (h x))
    {f : Ω → Fin K → ℝ} {g : Ω → F} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => h (f ω) (g ω)) := by
  let round : ℕ → (Fin K → ℝ) → (Fin K → ℤ) := fun m x i => ⌊((m + 1 : ℕ) : ℝ) * x i⌋
  let castZ : ℕ → (Fin K → ℤ) → (Fin K → ℝ) := fun m z i => (z i : ℝ) / ((m + 1 : ℕ) : ℝ)
  have h_approx_meas : ∀ m : ℕ, Measurable (fun ω => h (castZ m (round m (f ω))) (g ω)) := by
    intro m s hs
    have hpre : (fun ω => h (castZ m (round m (f ω))) (g ω)) ⁻¹' s =
        ⋃ z : Fin K → ℤ, ((fun ω => round m (f ω)) ⁻¹' {z}) ∩ (g ⁻¹' (h (castZ m z) ⁻¹' s)) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · intro hω; exact ⟨round m (f ω), rfl, hω⟩
      · rintro ⟨z, rfl, hω⟩; exact hω
    rw [hpre]
    refine MeasurableSet.iUnion (fun z => ?_)
    refine MeasurableSet.inter ?_ (hg (hh (castZ m z) hs))
    have hround_meas : Measurable (fun ω => round m (f ω)) := by
      refine measurable_pi_lambda _ (fun i => ?_)
      exact (measurable_const.mul ((measurable_pi_apply i).comp hf)).floor
    exact hround_meas (MeasurableSet.singleton z)
  have h_tend : ∀ ω, Tendsto (fun m : ℕ => h (castZ m (round m (f ω))) (g ω))
      atTop (𝓝 (h (f ω) (g ω))) := by
    intro ω
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun m hm => ?_⟩
    rw [dist_eq_norm]
    have hne := isNonExpansive_of_mh (hMH (g ω)).1 (hMH (g ω)).2 (castZ m (round m (f ω))) (f ω)
    have hnorm : ‖castZ m (round m (f ω)) - f ω‖ ≤ 1 / ((m + 1 : ℕ) : ℝ) := by
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      dsimp only [Pi.sub_apply, castZ, round]
      have hm_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hfl1 : (⌊((m + 1 : ℕ) : ℝ) * f ω i⌋ : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * f ω i := Int.floor_le _
      have hfl2 : ((m + 1 : ℕ) : ℝ) * f ω i < (⌊((m + 1 : ℕ) : ℝ) * f ω i⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · rw [le_sub_iff_add_le, le_div_iff₀ hm_pos]
        have : (-(1 / ((m + 1 : ℕ) : ℝ)) + f ω i) * ((m + 1 : ℕ) : ℝ) =
            -1 + ((m + 1 : ℕ) : ℝ) * f ω i := by
          field_simp
        rw [this]
        linarith
      · rw [sub_le_iff_le_add, div_le_iff₀ hm_pos]
        have : (1 / ((m + 1 : ℕ) : ℝ) + f ω i) * ((m + 1 : ℕ) : ℝ) =
            1 + ((m + 1 : ℕ) : ℝ) * f ω i := by
          field_simp
        rw [this]
        linarith
    have hmN : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 / ((N : ℝ) + 1) := by
      have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hle : (N : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; exact_mod_cast Nat.add_le_add_right hm 1
      exact one_div_le_one_div_of_le hpos hle
    exact lt_of_le_of_lt (le_trans hne hnorm) (lt_of_le_of_lt hmN hN)
  exact measurable_of_tendsto_metrizable h_approx_meas (tendsto_pi_nhds.mpr h_tend)

/-- Deterministic-start iterate `X^{[x]}_n(ω)`. -/
private noncomputable def mhDet {K : ℕ} {F : Type*} (h : (Fin K → ℝ) → F → Fin K → ℝ)
    (xi : ℕ → Ω → F) (n : ℕ) (ω : Ω) (x : Fin K → ℝ) : Fin K → ℝ :=
  mhIterate h xi (fun _ => x) n ω

omit [MeasurableSpace Ω] in
private lemma mhIterate_eq_mhDet {K : ℕ} {F : Type*} (h : (Fin K → ℝ) → F → Fin K → ℝ)
    (xi : ℕ → Ω → F) (Y : Ω → Fin K → ℝ) :
    ∀ n ω, mhIterate h xi Y n ω = mhDet h xi n ω (Y ω) := by
  intro n
  induction n with
  | zero => intro ω; rfl
  | succ n ih =>
    intro ω
    simp only [mhIterate, mhDet] at ih ⊢
    rw [ih ω]

omit [MeasurableSpace Ω] in
private lemma mhDet_mono {K : ℕ} {F : Type*} {h : (Fin K → ℝ) → F → Fin K → ℝ}
    (hMH : IsMHRecurrence h) (xi : ℕ → Ω → F) :
    ∀ n ω x y, x ≤ y → mhDet h xi n ω x ≤ mhDet h xi n ω y := by
  intro n
  induction n with
  | zero => intro ω x y hxy; exact hxy
  | succ n ih =>
    intro ω x y hxy
    exact (hMH (xi n ω)).1 _ _ (ih ω x y hxy)

omit [MeasurableSpace Ω] in
private lemma mhDet_hom {K : ℕ} {F : Type*} {h : (Fin K → ℝ) → F → Fin K → ℝ}
    (hMH : IsMHRecurrence h) (xi : ℕ → Ω → F) :
    ∀ n ω x (a : ℝ), mhDet h xi n ω (x + a • onesVec K) = a • onesVec K + mhDet h xi n ω x := by
  intro n
  induction n with
  | zero => intro ω x a; simp [mhDet, mhIterate, add_comm]
  | succ n ih =>
    intro ω x a
    simp only [mhDet, mhIterate] at ih ⊢
    rw [ih ω x a, add_comm (a • onesVec K)]
    exact (hMH (xi n ω)).2 (mhIterate h xi (fun _ => x) n ω) a

omit [MeasurableSpace Ω] in
private lemma mhDet_add {K : ℕ} {F : Type*} (h : (Fin K → ℝ) → F → Fin K → ℝ)
    (θ : Ω → Ω) (xi : ℕ → Ω → F) (xi0 : Ω → F)
    (hxi : ∀ (n : ℕ) (ω : Ω), xi n ω = xi0 (θ^[n] ω)) :
    ∀ m n ω x, mhDet h xi (m + n) ω x = mhDet h xi n (θ^[m] ω) (mhDet h xi m ω x) := by
  intro m n
  induction n with
  | zero => intro ω x; rfl
  | succ n ih =>
    intro ω x
    rw [Nat.add_succ]
    simp only [mhDet, mhIterate] at ih ⊢
    rw [ih ω x, hxi (m + n) ω, hxi n (θ^[m] ω), ← Function.iterate_add_apply, Nat.add_comm n m]

private lemma integrable_sup_fin {K : ℕ} [Nonempty (Fin K)] {μ : Measure Ω}
    {f : Ω → Fin K → ℝ} (hf : ∀ i, Integrable (fun ω => f ω i) μ) :
    Integrable (fun ω => ⨆ i : Fin K, f ω i) μ := by
  have heq : (fun ω => ⨆ i : Fin K, f ω i) =
      (fun ω => Finset.univ.sup' Finset.univ_nonempty (fun i => f ω i)) := by
    ext ω
    exact le_antisymm
      (ciSup_le (fun i => Finset.le_sup' (fun j => f ω j) (Finset.mem_univ i)))
      (Finset.sup'_le _ _ (fun i _ => le_ciSup (Finite.bddAbove_range _) i))
  rw [heq]
  have hfin : ∀ s : Finset (Fin K), ∀ hs : s.Nonempty,
      Integrable (fun ω => s.sup' hs (fun i => f ω i)) μ := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro hs; exact absurd hs Finset.not_nonempty_empty
    | @insert a s _ ih =>
      intro _
      by_cases hs : s.Nonempty
      · exact ((hf a).sup (ih hs)).congr (Eventually.of_forall (fun ω => by
          simpa using (Finset.sup'_insert hs (f := fun i => f ω i)).symm))
      · have hs_eq : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst hs_eq
        simpa using hf a
  exact hfin Finset.univ Finset.univ_nonempty

private lemma integrable_inf_fin {K : ℕ} [Nonempty (Fin K)] {μ : Measure Ω}
    {f : Ω → Fin K → ℝ} (hf : ∀ i, Integrable (fun ω => f ω i) μ) :
    Integrable (fun ω => ⨅ i : Fin K, f ω i) μ := by
  have heq : (fun ω => ⨅ i : Fin K, f ω i) =
      (fun ω => -(⨆ i : Fin K, -(f ω i))) := by
    ext ω
    refine le_antisymm ?_ ?_
    · rw [le_neg]
      exact ciSup_le (fun i => neg_le_neg (ciInf_le (Finite.bddBelow_range _) i))
    · refine le_ciInf (fun i => ?_)
      rw [neg_le]
      exact le_ciSup (Finite.bddAbove_range (fun j => -(f ω j))) i
  rw [heq]
  exact (integrable_sup_fin (fun i => (hf i).neg)).neg

end MHRecurrence

theorem solution {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} {F : Type*} [MeasurableSpace F]
    (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (θ : Ω ≃ᵐ Ω) (herg : Ergodic θ P0)
    (h : (Fin K → ℝ) → F → Fin K → ℝ) (hMH : IsMHRecurrence h)
    (hh : ∀ x : Fin K → ℝ, Measurable (h x))
    (xi : ℕ → Ω → F) (xi0 : Ω → F) (hxi0 : Measurable xi0)
    (hxi : ∀ (n : ℕ) (ω : Ω), xi n ω = xi0 ((θ : Ω → Ω)^[n] ω))
    (hint : ∀ n : ℕ, ∀ i : Fin K,
      Integrable (fun ω => mhIterate h xi (fun _ => (0 : Fin K → ℝ)) n ω i) P0)
    (Cst : ℝ) (hCst : 0 < Cst)
    (hlb : ∀ n : ℕ, ∀ i : Fin K,
      -(Cst * n) < ∫ ω, mhIterate h xi (fun _ => (0 : Fin K → ℝ)) n ω i ∂P0) :
    ∃ gbar glow : ℝ, ∀ Y : Ω → Fin K → ℝ, Integrable Y P0 →
      ((∀ᵐ ω ∂P0, Tendsto
          (fun n : ℕ => (⨆ i : Fin K, mhIterate h xi Y n ω i) / (n : ℝ)) atTop (𝓝 gbar)) ∧
       Tendsto
          (fun n : ℕ => (∫ ω, (⨆ i : Fin K, mhIterate h xi Y n ω i) ∂P0) / (n : ℝ))
          atTop (𝓝 gbar)) ∧
      ((∀ᵐ ω ∂P0, Tendsto
          (fun n : ℕ => (⨅ i : Fin K, mhIterate h xi Y n ω i) / (n : ℝ)) atTop (𝓝 glow)) ∧
       Tendsto
          (fun n : ℕ => (∫ ω, (⨅ i : Fin K, mhIterate h xi Y n ω i) ∂P0) / (n : ℝ))
          atTop (𝓝 glow)) := by
  have _ := hCst
  by_cases hK : K = 0
  · subst hK
    refine ⟨0, 0, fun Y _ => ?_⟩
    simp only [iSup, iInf, Set.range_eq_empty, Real.sSup_empty, Real.sInf_empty,
      zero_div, integral_zero]
    exact ⟨⟨Eventually.of_forall (fun _ => tendsto_const_nhds), tendsto_const_nhds⟩,
           ⟨Eventually.of_forall (fun _ => tendsto_const_nhds), tendsto_const_nhds⟩⟩
  · have : Nonempty (Fin K) := ⟨⟨0, Nat.pos_of_ne_zero hK⟩⟩
    have hT_mp : MeasurePreserving θ P0 P0 := herg.toMeasurePreserving
    let M : ℕ → Ω → ℝ := fun n ω => ⨆ i : Fin K, mhDet h xi n ω 0 i
    let m : ℕ → Ω → ℝ := fun n ω => ⨅ i : Fin K, mhDet h xi n ω 0 i
    have hM0 : ∀ ω, M 0 ω = 0 := by
      intro ω; simp [M, mhDet, mhIterate]
    have hm0 : ∀ ω, -m 0 ω = 0 := by
      intro ω; simp [m, mhDet, mhIterate]
    have hM_sub : ∀ a b ω, M (a + b) ω ≤ M a ω + M b ((θ : Ω → Ω)^[a] ω) := by
      intro a b ω
      refine ciSup_le (fun i => ?_)
      rw [mhDet_add h θ xi xi0 hxi a b ω 0]
      have hle : mhDet h xi a ω 0 ≤ 0 + (M a ω) • onesVec K := by
        intro j
        simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, onesVec, mul_one,
          zero_add]
        exact le_ciSup (Finite.bddAbove_range _) j
      have h1 := mhDet_mono hMH xi b ((θ : Ω → Ω)^[a] ω) _ _ hle i
      rw [mhDet_hom hMH xi b ((θ : Ω → Ω)^[a] ω) 0 (M a ω)] at h1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, onesVec, mul_one] at h1
      have h2 : mhDet h xi b ((θ : Ω → Ω)^[a] ω) 0 i ≤ M b ((θ : Ω → Ω)^[a] ω) :=
        le_ciSup (Finite.bddAbove_range _) i
      linarith
    have hm_sub : ∀ a b ω, -m (a + b) ω ≤ -m a ω + (-m b ((θ : Ω → Ω)^[a] ω)) := by
      intro a b ω
      suffices h' : m a ω + m b ((θ : Ω → Ω)^[a] ω) ≤ m (a + b) ω by linarith
      refine le_ciInf (fun i => ?_)
      rw [mhDet_add h θ xi xi0 hxi a b ω 0]
      have hge : 0 + (m a ω) • onesVec K ≤ mhDet h xi a ω 0 := by
        intro j
        simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, onesVec, mul_one,
          zero_add]
        exact ciInf_le (Finite.bddBelow_range _) j
      have h1 := mhDet_mono hMH xi b ((θ : Ω → Ω)^[a] ω) _ _ hge i
      rw [mhDet_hom hMH xi b ((θ : Ω → Ω)^[a] ω) 0 (m a ω)] at h1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, onesVec, mul_one] at h1
      have h2 : m b ((θ : Ω → Ω)^[a] ω) ≤ mhDet h xi b ((θ : Ω → Ω)^[a] ω) 0 i :=
        ciInf_le (Finite.bddBelow_range _) i
      linarith
    have hM_int : ∀ n, Integrable (M n) P0 := fun n => integrable_sup_fin (hint n)
    have hm_int : ∀ n, Integrable (m n) P0 := fun n => integrable_inf_fin (hint n)
    have hM_lb : ∀ n : ℕ, -(Cst * (n : ℝ)) ≤ ∫ ω, M n ω ∂P0 := by
      intro n
      have i0 : Fin K := Classical.arbitrary (Fin K)
      have h1 := le_of_lt (hlb n i0)
      have h2 : ∫ ω, mhDet h xi n ω 0 i0 ∂P0 ≤ ∫ ω, M n ω ∂P0 :=
        integral_mono (hint n i0) (hM_int n) (fun ω => le_ciSup (Finite.bddAbove_range _) i0)
      exact le_trans h1 h2
    have hneg_m_lb : ∀ n : ℕ, -((∫ ω, M 1 ω ∂P0) * (n : ℝ)) ≤ ∫ ω, (-m n ω) ∂P0 := by
      intro n
      have hm_le_M : ∀ ω, m n ω ≤ M n ω := by
        intro ω
        have i0 : Fin K := Classical.arbitrary (Fin K)
        exact le_trans (ciInf_le (Finite.bddBelow_range _) i0)
          (le_ciSup (Finite.bddAbove_range _) i0)
      have hM_le_birk : ∀ ω, M n ω ≤ birkhoffSum (θ : Ω → Ω) (M 1) n ω :=
        subadditive_le_birkhoffSum_one hM0 hM_sub n
      have hbirk_int : Integrable (birkhoffSum (θ : Ω → Ω) (M 1) n) P0 :=
        integrable_finsetSum _ (fun i _ => integrable_comp_iterate_equiv hT_mp (hM_int 1) i)
      have h_int_le : ∫ ω, m n ω ∂P0 ≤ (n : ℝ) * ∫ ω, M 1 ω ∂P0 := by
        calc ∫ ω, m n ω ∂P0
            ≤ ∫ ω, birkhoffSum (θ : Ω → Ω) (M 1) n ω ∂P0 :=
              integral_mono (hm_int n) hbirk_int (fun ω => le_trans (hm_le_M ω) (hM_le_birk ω))
          _ = ∑ i ∈ Finset.range n, ∫ ω, M 1 ((θ : Ω → Ω)^[i] ω) ∂P0 :=
              integral_finsetSum _ (fun i _ => integrable_comp_iterate_equiv hT_mp (hM_int 1) i)
          _ = (n : ℝ) * ∫ ω, M 1 ω ∂P0 := by
              simp only [integral_comp_iterate_equiv hT_mp (M 1), Finset.sum_const,
                Finset.card_range, nsmul_eq_mul]
      rw [integral_neg]
      linarith
    obtain ⟨gbar, hgbar_ae, hgbar_L1⟩ :=
      kingman_subadditive_ergodic P0 θ herg M hM0 hM_sub hM_int Cst hM_lb
    obtain ⟨nglow, hnglow_ae, hnglow_L1⟩ :=
      kingman_subadditive_ergodic P0 θ herg (fun n ω => -m n ω) hm0 hm_sub
        (fun n => (hm_int n).neg) (∫ ω, M 1 ω ∂P0) hneg_m_lb
    refine ⟨gbar, -nglow, fun Y hY => ?_⟩
    -- Integrability of Y coordinates, Ymax, Ymin, and mhIterate h xi Y n
    have hY_coord : ∀ i : Fin K, Integrable (fun ω => Y ω i) P0 := by
      intro i
      exact (ContinuousLinearMap.proj (R := ℝ) i).integrable_comp hY
    let Ymax : Ω → ℝ := fun ω => ⨆ j : Fin K, Y ω j
    let Ymin : Ω → ℝ := fun ω => ⨅ j : Fin K, Y ω j
    have hYmax_int : Integrable Ymax P0 := integrable_sup_fin hY_coord
    have hYmin_int : Integrable Ymin P0 := integrable_inf_fin hY_coord
    -- Pointwise sandwich for mhIterate h xi Y n
    have h_sand_M : ∀ n ω,
        Ymin ω + M n ω ≤ (⨆ i : Fin K, mhIterate h xi Y n ω i) ∧
        (⨆ i : Fin K, mhIterate h xi Y n ω i) ≤ Ymax ω + M n ω := by
      intro n ω
      have hY_ge : 0 + (Ymin ω) • onesVec K ≤ Y ω := by
        intro j
        simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, onesVec, mul_one,
          zero_add]
        exact ciInf_le (Finite.bddBelow_range _) j
      have hY_le : Y ω ≤ 0 + (Ymax ω) • onesVec K := by
        intro j
        simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, onesVec, mul_one,
          zero_add]
        exact le_ciSup (Finite.bddAbove_range _) j
      have hlo := mhDet_mono hMH xi n ω _ _ hY_ge
      rw [mhDet_hom hMH xi n ω 0 (Ymin ω), ← mhIterate_eq_mhDet] at hlo
      have hhi := mhDet_mono hMH xi n ω _ _ hY_le
      rw [mhDet_hom hMH xi n ω 0 (Ymax ω), ← mhIterate_eq_mhDet] at hhi
      constructor
      · rw [add_comm, ← le_sub_iff_add_le]
        refine ciSup_le (fun i => ?_)
        rw [le_sub_iff_add_le]
        have hi := hlo i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, onesVec, mul_one] at hi
        have hsup : mhIterate h xi Y n ω i ≤ ⨆ j : Fin K, mhIterate h xi Y n ω j :=
          le_ciSup (Finite.bddAbove_range _) i
        linarith
      · refine ciSup_le (fun i => ?_)
        have hi := hhi i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, onesVec, mul_one] at hi
        have hsup : mhDet h xi n ω 0 i ≤ M n ω := le_ciSup (Finite.bddAbove_range _) i
        linarith
    have h_sand_m : ∀ n ω,
        Ymin ω + m n ω ≤ (⨅ i : Fin K, mhIterate h xi Y n ω i) ∧
        (⨅ i : Fin K, mhIterate h xi Y n ω i) ≤ Ymax ω + m n ω := by
      intro n ω
      have hY_ge : 0 + (Ymin ω) • onesVec K ≤ Y ω := by
        intro j
        simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, onesVec, mul_one,
          zero_add]
        exact ciInf_le (Finite.bddBelow_range _) j
      have hY_le : Y ω ≤ 0 + (Ymax ω) • onesVec K := by
        intro j
        simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, onesVec, mul_one,
          zero_add]
        exact le_ciSup (Finite.bddAbove_range _) j
      have hlo := mhDet_mono hMH xi n ω _ _ hY_ge
      rw [mhDet_hom hMH xi n ω 0 (Ymin ω), ← mhIterate_eq_mhDet] at hlo
      have hhi := mhDet_mono hMH xi n ω _ _ hY_le
      rw [mhDet_hom hMH xi n ω 0 (Ymax ω), ← mhIterate_eq_mhDet] at hhi
      constructor
      · refine le_ciInf (fun i => ?_)
        have hi := hlo i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, onesVec, mul_one] at hi
        have hinf : m n ω ≤ mhDet h xi n ω 0 i := ciInf_le (Finite.bddBelow_range _) i
        linarith
      · rw [add_comm, ← sub_le_iff_le_add]
        refine le_ciInf (fun i => ?_)
        rw [sub_le_iff_le_add]
        have hi := hhi i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, onesVec, mul_one] at hi
        have hinf : (⨅ j : Fin K, mhIterate h xi Y n ω j) ≤ mhIterate h xi Y n ω i :=
          ciInf_le (Finite.bddBelow_range _) i
        linarith
    -- AEStronglyMeasurable & Integrable for mhIterate h xi Y n
    have hxi_meas : ∀ n, Measurable (xi n) := by
      intro n
      have hfun : xi n = fun ω => xi0 ((θ : Ω → Ω)^[n] ω) := funext (hxi n)
      rw [hfun]
      exact hxi0.comp (θ.measurable.iterate n)
    have hY_iter_aem : ∀ n, AEStronglyMeasurable (mhIterate h xi Y n) P0 := by
      let Y' : Ω → Fin K → ℝ := hY.aestronglyMeasurable.mk Y
      have hY'_meas : Measurable Y' := hY.aestronglyMeasurable.stronglyMeasurable_mk.measurable
      have hY_ae : Y =ᵐ[P0] Y' := hY.aestronglyMeasurable.ae_eq_mk
      have h_iter_meas : ∀ n, Measurable (mhIterate h xi Y' n) := by
        intro n
        induction n with
        | zero => exact hY'_meas
        | succ n ih => exact measurable_comp_caratheodory h hMH hh ih (hxi_meas n)
      intro n
      refine (h_iter_meas n).aestronglyMeasurable.congr ?_
      filter_upwards [hY_ae] with ω hω
      rw [mhIterate_eq_mhDet, mhIterate_eq_mhDet, hω]
    have hY_coord_int : ∀ n, ∀ i : Fin K, Integrable (fun ω => mhIterate h xi Y n ω i) P0 := by
      intro n i
      refine Integrable.mono'
        ((hYmin_int.abs.add hYmax_int.abs).add (hint n i).abs)
        (((continuous_apply i).comp_aestronglyMeasurable (hY_iter_aem n))) ?_
      refine Eventually.of_forall (fun ω => ?_)
      have hY_ge : 0 + (Ymin ω) • onesVec K ≤ Y ω := by
        intro j; simp [Ymin, onesVec]; exact ciInf_le (Finite.bddBelow_range _) j
      have hY_le : Y ω ≤ 0 + (Ymax ω) • onesVec K := by
        intro j; simp [Ymax, onesVec]; exact le_ciSup (Finite.bddAbove_range _) j
      have hlo := mhDet_mono hMH xi n ω _ _ hY_ge i
      rw [mhDet_hom hMH xi n ω 0 (Ymin ω), ← mhIterate_eq_mhDet] at hlo
      have hhi := mhDet_mono hMH xi n ω _ _ hY_le i
      rw [mhDet_hom hMH xi n ω 0 (Ymax ω), ← mhIterate_eq_mhDet] at hhi
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, onesVec, mul_one, mhDet] at hlo hhi
      simp only [Pi.add_apply, Real.norm_eq_abs, abs_le]
      have := le_abs_self (Ymin ω); have := neg_le_abs (Ymin ω)
      have := le_abs_self (Ymax ω); have := neg_le_abs (Ymax ω)
      have := le_abs_self (mhIterate h xi (fun _ => 0) n ω i)
      have := neg_le_abs (mhIterate h xi (fun _ => 0) n ω i)
      constructor <;> linarith
    have hY_M_int : ∀ n, Integrable (fun ω => ⨆ i : Fin K, mhIterate h xi Y n ω i) P0 :=
      fun n => integrable_sup_fin (hY_coord_int n)
    have hY_m_int : ∀ n, Integrable (fun ω => ⨅ i : Fin K, mhIterate h xi Y n ω i) P0 :=
      fun n => integrable_inf_fin (hY_coord_int n)
    -- Squeeze theorem for all 4 limits
    have hglow_ae : ∀ᵐ ω ∂P0, Tendsto (fun n : ℕ => m n ω / (n : ℝ)) atTop (𝓝 (-nglow)) := by
      filter_upwards [hnglow_ae] with ω hω
      simpa [neg_div] using hω.neg
    have hglow_L1 : Tendsto (fun n : ℕ => (∫ ω, m n ω ∂P0) / (n : ℝ)) atTop (𝓝 (-nglow)) := by
      simpa [integral_neg, neg_div] using hnglow_L1.neg
    have squeeze_div : ∀ (a b : ℕ → ℝ) (c₁ c₂ L : ℝ),
        Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 L) →
        (∀ n : ℕ, c₁ + a n ≤ b n ∧ b n ≤ c₂ + a n) →
        Tendsto (fun n : ℕ => b n / (n : ℝ)) atTop (𝓝 L) := by
      intro a b c₁ c₂ L ha hsand
      have hlo : Tendsto (fun n : ℕ => c₁ / (n : ℝ) + a n / (n : ℝ)) atTop (𝓝 (0 + L)) :=
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add ha
      have hhi : Tendsto (fun n : ℕ => c₂ / (n : ℝ) + a n / (n : ℝ)) atTop (𝓝 (0 + L)) :=
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add ha
      rw [zero_add] at hlo hhi
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
        rw [← add_div]
        exact div_le_div_of_nonneg_right (hsand n).1 (le_of_lt hn_pos)
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
        rw [← add_div]
        exact div_le_div_of_nonneg_right (hsand n).2 (le_of_lt hn_pos)
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · filter_upwards [hgbar_ae] with ω hω
      exact squeeze_div (fun n => M n ω) (fun n => ⨆ i : Fin K, mhIterate h xi Y n ω i)
        (Ymin ω) (Ymax ω) gbar hω (fun n => h_sand_M n ω)
    · refine squeeze_div (fun n => ∫ ω, M n ω ∂P0)
        (fun n => ∫ ω, (⨆ i : Fin K, mhIterate h xi Y n ω i) ∂P0)
        (∫ ω, Ymin ω ∂P0) (∫ ω, Ymax ω ∂P0) gbar hgbar_L1 (fun n => ⟨?_, ?_⟩)
      · rw [← integral_add hYmin_int (hM_int n)]
        exact integral_mono (hYmin_int.add (hM_int n)) (hY_M_int n) (fun ω => (h_sand_M n ω).1)
      · rw [← integral_add hYmax_int (hM_int n)]
        exact integral_mono (hY_M_int n) (hYmax_int.add (hM_int n)) (fun ω => (h_sand_M n ω).2)
    · filter_upwards [hglow_ae] with ω hω
      exact squeeze_div (fun n => m n ω) (fun n => ⨅ i : Fin K, mhIterate h xi Y n ω i)
        (Ymin ω) (Ymax ω) (-nglow) hω (fun n => h_sand_m n ω)
    · refine squeeze_div (fun n => ∫ ω, m n ω ∂P0)
        (fun n => ∫ ω, (⨅ i : Fin K, mhIterate h xi Y n ω i) ∂P0)
        (∫ ω, Ymin ω ∂P0) (∫ ω, Ymax ω ∂P0) (-nglow) hglow_L1 (fun n => ⟨?_, ?_⟩)
      · rw [← integral_add hYmin_int (hm_int n)]
        exact integral_mono (hYmin_int.add (hm_int n)) (hY_m_int n) (fun ω => (h_sand_m n ω).1)
      · rw [← integral_add hYmax_int (hm_int n)]
        exact integral_mono (hY_m_int n) (hYmax_int.add (hm_int n)) (fun ω => (h_sand_m n ω).2)

#print axioms solution
