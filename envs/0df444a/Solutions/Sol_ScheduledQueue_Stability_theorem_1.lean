-- Prove2me | solution 1 for ScheduledQueue.Stability.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T22:02:18.861396+00:00
-- url     : https://prove2.me/submissions/2ca38c86-223d-4496-9387-648e692ec7c7

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed
import Theorems.Thm_ScheduledQueue_Stability_loynes_representation
import Theorems.Thm_ScheduledQueue_Stability_sufficiency
import Theorems.Thm_ScheduledQueue_Stability_necessity

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace SQMainAux

theorem bc_eventually_lt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : ℝ} (hh : 0 < h) {W : Ω → ℝ} (hW : Integrable W P)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ n, IdentDistrib (Z n) W P P) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, Z n ω < n * h := by
  set X : Ω → ℝ := fun ω => max (W ω / h + 1) 0
  have hXint : Integrable X P := ((hW.div_const h).add (integrable_const 1)).pos_part
  have hX0 : 0 ≤ X := fun ω => le_max_right _ _
  have hfin : (∑' n : ℕ, P {ω | X ω ∈ Ioi (n : ℝ)}) < ∞ := by
    let _ : MeasureSpace Ω := ⟨P⟩
    exact tsum_prob_mem_Ioi_lt_top hXint hX0
  have hle : ∀ n : ℕ, P {ω | (n : ℝ) * h ≤ Z n ω} ≤ P {ω | X ω ∈ Ioi (n : ℝ)} := by
    intro n
    have e : P {ω | (n : ℝ) * h ≤ Z n ω} = P {ω | (n : ℝ) * h ≤ W ω} :=
      (hZ n).measure_mem_eq (s := {x | (n : ℝ) * h ≤ x}) (measurableSet_le measurable_const measurable_id)
    rw [e]
    apply measure_mono
    intro ω hω
    simp only [mem_setOf_eq, mem_Ioi, X] at hω ⊢
    have : (n : ℝ) ≤ W ω / h := by rw [le_div_iff₀ hh]; linarith
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hsum : (∑' n : ℕ, P {ω | (n : ℝ) * h ≤ Z n ω}) ≠ ∞ :=
    (lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) hfin).ne
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  simpa using hn

open ScheduledQueue.Stability

/-- Almost surely every reversed count `#{j : R_j ∈ (0,s]}` is finite. -/
theorem revCount_finite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, revCount h ξ U s ω ≠ ⊤ := by
  have hU : ∀ᵐ ω ∂P, U ω ∈ Icc (0 : ℝ) 1 := by
    rw [hin.uniform.ae_iff (p := fun x => x ∈ Icc (0 : ℝ) 1) measurableSet_Icc.mem]
    exact ae_restrict_mem measurableSet_Icc
  have h1 : ∀ K : ℕ, ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop, ξ (m : ℤ) ω + K < m * h := by
    intro K
    apply bc_eventually_lt hh (W := fun ω => ξ 0 ω + K)
      (hin.integrable.add (integrable_const _))
    intro m
    exact (hin.identDistrib (m : ℤ)).comp (u := fun x : ℝ => x + (K : ℝ)) (by fun_prop)
  have h2 : ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop, -ξ (-(m : ℤ)) ω + h < m * h := by
    apply bc_eventually_lt hh (W := fun ω => -ξ 0 ω + h)
      (hin.integrable.neg.add (integrable_const _))
    intro m
    exact (hin.identDistrib _).comp (u := fun x => -x + h) (by fun_prop)
  rw [← ae_all_iff] at h1
  filter_upwards [h1, h2, hU] with ω h1 h2 hU
  intro s
  obtain ⟨K, hK⟩ := exists_nat_ge s
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (h1 K)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 h2
  have hsub : {j : ℤ | revArrival h ξ U j ω ∈ Ioc 0 s} ⊆
      (Finset.Icc (-(N2 : ℤ)) N1 : Set ℤ) := by
    intro j ⟨hj1, hj2⟩
    simp only [revArrival] at hj1 hj2
    simp only [Finset.coe_Icc, mem_Icc]
    constructor
    · by_contra hc
      have hm := hN2 (-j).toNat (by omega)
      have e : (-(((-j).toNat : ℕ) : ℤ)) = j := by omega
      have e2 : (((-j).toNat : ℕ) : ℝ) = -(j : ℝ) := by
        have : (((-j).toNat : ℕ) : ℤ) = -j := by omega
        exact_mod_cast this
      rw [e, e2] at hm
      nlinarith [hU.2]
    · by_contra hc
      have hm := hN1 j.toNat (by omega)
      have e : ((j.toNat : ℕ) : ℤ) = j := by omega
      have e2 : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by exact_mod_cast e
      rw [e, e2] at hm
      nlinarith [hU.1]
  exact ((Finset.finite_toSet _).subset hsub).encard_lt_top.ne

end SQMainAux

open ScheduledQueue.Stability SQMainAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledInput P ξ U) :
    (∃ ν : ProbabilityMeasure ℝ,
        TendstoInDistribution (fun t : ℝ => workload h ξ U t) atTop id (fun _ => P)
          (ν : Measure ℝ)) ↔
      ∃ c : ℝ, ∀ᵐ ω ∂P, ξ 0 ω ≤ c := by
  set M : ℝ → Ω → ℝ := fun t => revMax h ξ U t
  set W : ℝ → Ω → ℝ := fun t => workload h ξ U t
  -- negative times: both processes vanish
  have hMneg : ∀ t : ℝ, t < 0 → M t = fun _ => 0 := by
    intro t ht; funext ω
    have : IsEmpty (Icc (0 : ℝ) t) := Set.isEmpty_coe_sort.2 (Icc_eq_empty (by linarith))
    simp only [M, revMax]
    exact Real.iSup_of_isEmpty _
  have hWneg : ∀ t : ℝ, t < 0 → W t = fun _ => 0 := by
    intro t ht; funext ω
    have : IsEmpty (Icc (0 : ℝ) t) := Set.isEmpty_coe_sort.2 (Icc_eq_empty (by linarith))
    simp only [W, workload]
    exact Real.iSup_of_isEmpty _
  have hWM : ∀ t : ℝ, IdentDistrib (W t) (M t) P P := by
    intro t
    rcases lt_or_ge t 0 with ht | ht
    · rw [hWneg t ht, hMneg t ht]; exact IdentDistrib.refl aemeasurable_const
    · exact loynes_representation P h hh ξ U hin t ht
  have hMmeas : ∀ t, AEMeasurable (M t) P := fun t => (hWM t).aemeasurable_snd
  have hWmeas : ∀ t, AEMeasurable (W t) P := fun t => (hWM t).aemeasurable_fst
  -- deterministic facts on the event where all reversed counts are finite
  have hLam0 : ∀ ω, Lam h ξ U 0 ω - 0 = 0 := by
    intro ω; simp [Lam, revCount]
  have hbdd : ∀ ω, (∀ s : ℝ, revCount h ξ U s ω ≠ ⊤) → ∀ t : ℝ,
      BddAbove (range fun s : Icc (0 : ℝ) t => Lam h ξ U s ω - s) := by
    intro ω hf t
    refine ⟨h * (revCount h ξ U t ω).toNat, ?_⟩
    rintro _ ⟨⟨s, hs0, hst⟩, rfl⟩
    have hle : revCount h ξ U s ω ≤ revCount h ξ U t ω :=
      encard_le_encard (fun j hj => ⟨hj.1, hj.2.trans hst⟩)
    have : ((revCount h ξ U s ω).toNat : ℝ) ≤ (revCount h ξ U t ω).toNat := by
      exact_mod_cast ENat.toNat_le_toNat hle (hf t)
    simp only [Lam]
    nlinarith
  have hleM : ∀ ω, (∀ s : ℝ, revCount h ξ U s ω ≠ ⊤) → ∀ t s : ℝ, 0 ≤ s → s ≤ t →
      Lam h ξ U s ω - s ≤ M t ω := by
    intro ω hf t s hs hst
    exact le_ciSup (f := fun s : Icc (0 : ℝ) t => Lam h ξ U s ω - s) (hbdd ω hf t) ⟨s, hs, hst⟩
  have hMnn : ∀ ω, (∀ s : ℝ, revCount h ξ U s ω ≠ ⊤) → ∀ t : ℝ, 0 ≤ M t ω := by
    intro ω hf t
    rcases lt_or_ge t 0 with ht | ht
    · rw [hMneg t ht]
    · have := hleM ω hf t 0 le_rfl ht
      rwa [hLam0] at this
  have hmono : ∀ ω, (∀ s : ℝ, revCount h ξ U s ω ≠ ⊤) → Monotone fun t => M t ω := by
    intro ω hf t t' htt'
    rcases lt_or_ge t 0 with ht | ht
    · simp only [hMneg t ht]; exact hMnn ω hf t'
    · haveI : Nonempty (Icc (0 : ℝ) t) := ⟨⟨0, le_rfl, ht⟩⟩
      apply ciSup_le
      rintro ⟨s, hs0, hst⟩
      exact hleM ω hf t' s hs0 (hst.trans htt')
  have hfin := revCount_finite P h hh ξ U hin
  constructor
  · -- only if
    rintro ⟨ν, hν⟩
    by_contra hnot
    have hnec := necessity P h hh ξ U hin hnot
    have htop : ∀ᵐ ω ∂P, Tendsto (fun t => M t ω) atTop atTop := by
      filter_upwards [hfin, hnec] with ω hf hn
      rw [tendsto_atTop]
      intro C
      obtain ⟨s, hs, hC⟩ := hn C
      filter_upwards [eventually_ge_atTop s] with t ht
      exact hC.le.trans (hleM ω hf t s hs ht)
    have hzero : ∀ x : ℝ, (ν : Measure ℝ) (Iio x) = 0 := by
      intro x
      have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν.tendsto
        (isOpen_Iio (a := x))
      simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at hlim
      have hT : Tendsto (fun t => (P.map (W t)) (Iio x)) atTop (𝓝 0) := by
        have e : ∀ t, (P.map (W t)) (Iio x) = ∫⁻ ω, (Iio x).indicator 1 (M t ω) ∂P := by
          intro t
          rw [(hWM t).map_eq, ← lintegral_indicator_one measurableSet_Iio,
            lintegral_map' (measurable_one.indicator measurableSet_Iio).aemeasurable (hMmeas t)]
        simp_rw [e]
        have h0 : (0 : ℝ≥0∞) = ∫⁻ ω, (0 : Ω → ℝ≥0∞) ω ∂P := by simp
        rw [h0]
        apply tendsto_lintegral_filter_of_dominated_convergence' (fun _ => 1)
        · exact Eventually.of_forall fun t =>
            (measurable_one.indicator measurableSet_Iio).comp_aemeasurable (hMmeas t)
        · exact Eventually.of_forall fun t => Eventually.of_forall fun ω =>
            indicator_le_self' (fun _ _ => zero_le_one) _
        · simp
        · filter_upwards [htop] with ω hω
          apply tendsto_const_nhds.congr'
          filter_upwards [hω.eventually_ge_atTop x] with t ht
          simp [Set.indicator, not_lt.2 ht]
      rw [hT.liminf_eq] at hlim
      exact le_antisymm hlim bot_le
    have huniv : (ν : Measure ℝ) univ = 0 := by
      have : (univ : Set ℝ) = ⋃ n : ℕ, Iio (n : ℝ) := by
        ext x; simp only [mem_univ, mem_iUnion, mem_Iio, true_iff]
        exact exists_nat_gt x
      rw [this]
      exact measure_iUnion_null fun n => hzero n
    simp at huniv
  · -- if
    intro hc
    have hsuf := sufficiency P h hh ξ U hin hc
    have hgood : ∀ᵐ ω ∂P, (∀ s : ℝ, revCount h ξ U s ω ≠ ⊤) ∧
        BddAbove (range fun t => M t ω) := by
      filter_upwards [hsuf] with ω ⟨C, hC⟩
      have hf : ∀ s : ℝ, revCount h ξ U s ω ≠ ⊤ := by
        intro s
        rcases lt_or_ge s 0 with hs | hs
        · have : revCount h ξ U s ω = 0 := by
            simp only [revCount, encard_eq_zero]
            ext j; simp only [mem_setOf_eq, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
            intro h1; linarith
          rw [this]; exact ENat.zero_ne_top
        · exact (hC s hs).1
      refine ⟨hf, ⟨max C 0, ?_⟩⟩
      rintro _ ⟨t, rfl⟩
      rcases lt_or_ge t 0 with ht | ht
      · simp only [hMneg t ht]; exact le_max_right _ _
      · haveI : Nonempty (Icc (0 : ℝ) t) := ⟨⟨0, le_rfl, ht⟩⟩
        apply ciSup_le
        rintro ⟨s, hs0, hst⟩
        exact (hC s hs0).2.trans (le_max_left _ _)
    set Z : Ω → ℝ := fun ω => ⨆ t : ℝ, M t ω
    have hconv : ∀ᵐ ω ∂P, Tendsto (fun t => M t ω) atTop (𝓝 (Z ω)) := by
      filter_upwards [hgood] with ω ⟨hf, hb⟩
      exact tendsto_atTop_ciSup (hmono ω hf) hb
    have hZ : AEMeasurable Z P := by
      apply aemeasurable_of_tendsto_metrizable_ae' (f := fun n : ℕ => M n) (fun n => hMmeas n)
      filter_upwards [hconv] with ω hω
      exact hω.comp tendsto_natCast_atTop_atTop
    have hTD : TendstoInDistribution M atTop Z (fun _ => P) P :=
      tendstoInDistribution_of_ae_tendsto hMmeas hZ hconv
    obtain ⟨ν, hνdef⟩ : ∃ ν : ProbabilityMeasure ℝ, (ν : Measure ℝ) = P.map Z :=
      ⟨⟨_, Measure.isProbabilityMeasure_map hZ⟩, rfl⟩
    refine ⟨ν, ?_⟩
    refine ⟨hWmeas, measurable_id.aemeasurable, ?_⟩
    have e1 : (fun t => (⟨P.map (W t), Measure.isProbabilityMeasure_map (hWmeas t)⟩ :
        ProbabilityMeasure ℝ)) = fun t => ⟨P.map (M t), Measure.isProbabilityMeasure_map (hMmeas t)⟩ := by
      funext t; apply Subtype.ext; exact (hWM t).map_eq
    rw [e1]
    convert hTD.tendsto using 2
    congr 1
    exact Subtype.ext (by simp only [Measure.map_id, hνdef])
