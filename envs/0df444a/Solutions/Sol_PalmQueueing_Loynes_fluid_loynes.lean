-- Prove2me | solution 1 for PalmQueueing.Loynes.fluid_loynes
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:20:30.11893+00:00
-- url     : https://prove2.me/submissions/025f65c5-2787-49d2-bbe9-f982022e8e09

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Loynes_SingleServerQueue
import Definitions.Def_PalmQueueing_Loynes_FluidQueue
import Definitions.Def_PalmQueueing_Loynes_StationaryRegime

open MeasureTheory Filter Topology
open PalmQueueing.Palm PalmQueueing.Loynes

section Helpers

variable {Ω : Type*} [MeasurableSpace Ω]

private lemma flowMeasure_self {θ : Flow Ω} {m : ℝ → ℝ → Ω → ℝ} (hm : IsFlowMeasure θ m)
    (t : ℝ) (ω : Ω) : m t t ω = 0 := by
  have h := hm.2.1 t t t ω le_rfl le_rfl
  linarith

private lemma flowMeasure_shift {θ : Flow Ω} {m : ℝ → ℝ → Ω → ℝ} (hm : IsFlowMeasure θ m)
    {s t : ℝ} (hst : s ≤ t) (r : ℝ) (ω : Ω) :
    m s t (θ r ω) = m (s + r) (t + r) ω := by
  rw [hm.2.2.1 s t (θ r ω) hst, hm.2.2.1 (s + r) (t + r) ω (by linarith)]
  have hθ : θ (s + r) ω = θ s (θ r ω) := congrFun (θ.map_add s r) ω
  rw [hθ]
  ring_nf

private lemma flowMeasure_mono_left {θ : Flow Ω} {m : ℝ → ℝ → Ω → ℝ} (hm : IsFlowMeasure θ m)
    {s₁ s₂ t : ℝ} (h12 : s₁ ≤ s₂) (h2t : s₂ ≤ t) (ω : Ω) :
    m s₂ t ω ≤ m s₁ t ω := by
  rw [hm.2.1 s₁ s₂ t ω h12 h2t]
  linarith [hm.1 s₁ s₂ ω h12]

private lemma flowMeasure_mono_right {θ : Flow Ω} {m : ℝ → ℝ → Ω → ℝ} (hm : IsFlowMeasure θ m)
    {s t₁ t₂ : ℝ} (hs1 : s ≤ t₁) (h12 : t₁ ≤ t₂) (ω : Ω) :
    m s t₁ ω ≤ m s t₂ ω := by
  rw [hm.2.1 s t₁ t₂ ω hs1 h12]
  linarith [hm.1 t₁ t₂ ω h12]

private lemma flow_iterate_neg_one (θ : Flow Ω) (n : ℕ) (ω : Ω) :
    (θ (-1))^[n] ω = θ (-(n : ℝ)) ω := by
  induction n with
  | zero =>
    simp [θ.map_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have h : θ (-1 + -(n : ℝ)) ω = θ (-1) (θ (-(n : ℝ)) ω) :=
      congrFun (θ.map_add (-1) (-(n : ℝ))) ω
    rw [← h]
    congr 1
    push_cast
    ring

private lemma birkhoffSum_flowMeasure {θ : Flow Ω} {m : ℝ → ℝ → Ω → ℝ} (hm : IsFlowMeasure θ m)
    (n : ℕ) (ω : Ω) :
    birkhoffSum (θ (-1)) (m (-1) 0) n ω = m (-(n : ℝ)) 0 ω := by
  induction n with
  | zero =>
    simp [birkhoffSum_zero, flowMeasure_self hm]
  | succ n ih =>
    rw [birkhoffSum_succ, ih, flow_iterate_neg_one,
      flowMeasure_shift hm (by norm_num : (-1 : ℝ) ≤ 0)]
    have h1 : (-1 : ℝ) + -(n : ℝ) = -((n + 1 : ℕ) : ℝ) := by push_cast; ring
    have h2 : (0 : ℝ) + -(n : ℝ) = -(n : ℝ) := by ring
    rw [h1, h2]
    have hadd := hm.2.1 (-((n + 1 : ℕ) : ℝ)) (-(n : ℝ)) 0 ω (by push_cast; linarith) (by linarith)
    linarith

private lemma maximal_ergodic_theorem {P : Measure Ω} [IsFiniteMeasure P]
    {T : Ω → Ω} (hT : MeasurePreserving T P P)
    {f : Ω → ℝ} (hf_meas : Measurable f) (hf : Integrable f P) :
    0 ≤ ∫ ω in {ω | ∃ k : ℕ, 1 ≤ k ∧ 0 < birkhoffSum T f k ω}, f ω ∂P := by
  let S : ℕ → Ω → ℝ := fun k ω => birkhoffSum T f k ω
  have hS_meas : ∀ k, Measurable (S k) := by
    intro k
    induction k with
    | zero =>
      simp only [S, birkhoffSum_zero']
      exact measurable_const
    | succ k ih =>
      have heq : S (k + 1) = fun ω => S k ω + f (T^[k] ω) := by
        ext ω; exact birkhoffSum_succ T f k ω
      rw [heq]
      exact ih.add (hf_meas.comp (hT.measurable.iterate k))
  have hS_int : ∀ k, Integrable (S k) P := by
    intro k
    induction k with
    | zero =>
      simp [S, birkhoffSum_zero']
    | succ k ih =>
      have hcomp : Integrable (fun ω => f (T^[k] ω)) P :=
        (hT.iterate k).integrable_comp_of_integrable hf
      have heq : S (k + 1) = fun ω => S k ω + f (T^[k] ω) := by
        ext ω; exact birkhoffSum_succ T f k ω
      rw [heq]
      exact ih.add hcomp
  let M : ℕ → Ω → ℝ := fun N ω =>
    (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun k => S k ω)
  have hM_nonneg : ∀ N ω, 0 ≤ M N ω := by
    intro N ω
    have h0 : (0 : ℕ) ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.succ_pos N)
    have hle := Finset.le_sup' (f := fun k => S k ω) h0
    simpa [S, birkhoffSum_zero] using hle
  have hM_int : ∀ N, Integrable (M N) P := by
    intro N
    induction N with
    | zero =>
      have heq : M 0 = S 0 := by ext ω; simp [M, S]
      rw [heq]
      exact hS_int 0
    | succ N ih =>
      have heq : M (N + 1) = fun ω => max (M N ω) (S (N + 1) ω) := by
        ext ω
        simp only [M, Finset.range_add_one]
        rw [Finset.sup'_insert]
        exact max_comm _ _
      rw [heq]
      exact ih.sup (hS_int (N + 1))
  let E : ℕ → Set Ω := fun N => {ω | ∃ k, 1 ≤ k ∧ k ≤ N ∧ 0 < S k ω}
  have hE_meas : ∀ N, MeasurableSet (E N) := by
    intro N
    have heq : E N = ⋃ k ∈ Finset.Icc 1 N, {ω | 0 < S k ω} := by
      ext ω
      simp only [E, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_Icc, exists_prop]
      tauto
    rw [heq]
    exact Finset.measurableSet_biUnion _ fun k _ => measurableSet_lt measurable_const (hS_meas k)
  have hstep : ∀ N, 0 ≤ ∫ ω in E N, f ω ∂P := by
    intro N
    have hpt : ∀ ω ∈ E N, M N ω - M N (T ω) ≤ f ω := by
      intro ω hω
      rcases hω with ⟨k₀, hk₀1, hk₀N, hk₀pos⟩
      have hMle : M N ω ≤ f ω + M N (T ω) := by
        refine Finset.sup'_le _ _ fun k hk => ?_
        have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rcases eq_or_ne k 0 with rfl | hk0
        · have h1 : S 0 ω < S k₀ ω := by simpa [S, birkhoffSum_zero] using hk₀pos
          have hk₀' : k₀ - 1 ∈ Finset.range (N + 1) :=
            Finset.mem_range.mpr (by omega)
          have h2 : S k₀ ω = f ω + S (k₀ - 1) (T ω) := by
            have := birkhoffSum_succ' T f (k₀ - 1) ω
            rw [Nat.sub_add_cancel hk₀1] at this
            exact this
          have h3 : S (k₀ - 1) (T ω) ≤ M N (T ω) :=
            Finset.le_sup' (f := fun j => S j (T ω)) hk₀'
          linarith
        · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
          have hk' : k - 1 ∈ Finset.range (N + 1) :=
            Finset.mem_range.mpr (by omega)
          have h2 : S k ω = f ω + S (k - 1) (T ω) := by
            have := birkhoffSum_succ' T f (k - 1) ω
            rw [Nat.sub_add_cancel hk1] at this
            exact this
          have h3 : S (k - 1) (T ω) ≤ M N (T ω) :=
            Finset.le_sup' (f := fun j => S j (T ω)) hk'
          linarith
      linarith
    have hM_zero_compl : ∀ ω, ω ∉ E N → M N ω = 0 := by
      intro ω hω
      apply le_antisymm _ (hM_nonneg N ω)
      refine Finset.sup'_le _ _ fun k hk => ?_
      have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rcases eq_or_ne k 0 with rfl | hk0
      · simp [S, birkhoffSum_zero]
      · by_contra hlt
        exact hω ⟨k, Nat.one_le_iff_ne_zero.mpr hk0, hkN, lt_of_not_ge hlt⟩
    have hMT_int : Integrable (fun ω => M N (T ω)) P :=
      hT.integrable_comp_of_integrable (hM_int N)
    have h1 : ∫ ω in E N, (M N ω - M N (T ω)) ∂P ≤ ∫ ω in E N, f ω ∂P :=
      setIntegral_mono_on ((hM_int N).sub hMT_int).integrableOn hf.integrableOn (hE_meas N) hpt
    have h2 : ∫ ω in E N, (M N ω - M N (T ω)) ∂P =
        (∫ ω in E N, M N ω ∂P) - ∫ ω in E N, M N (T ω) ∂P :=
      integral_sub (hM_int N).integrableOn hMT_int.integrableOn
    have h3 : ∫ ω in E N, M N ω ∂P = ∫ ω, M N ω ∂P := by
      rw [← integral_indicator (hE_meas N)]
      congr 1; ext ω
      by_cases hω : ω ∈ E N
      · simp [hω]
      · simp [hω, hM_zero_compl ω hω]
    have h4 : ∫ ω in E N, M N (T ω) ∂P ≤ ∫ ω, M N (T ω) ∂P :=
      setIntegral_le_integral hMT_int (Eventually.of_forall fun ω => hM_nonneg N (T ω))
    have h5 : ∫ ω, M N (T ω) ∂P = ∫ ω, M N ω ∂P := by
      have hm_aesm : AEStronglyMeasurable (M N) (Measure.map T P) := by
        rw [hT.map_eq]
        exact (hM_int N).aestronglyMeasurable
      have := integral_map hT.measurable.aemeasurable hm_aesm
      rw [hT.map_eq] at this
      exact this.symm
    linarith
  let E_all : Set Ω := {ω | ∃ k : ℕ, 1 ≤ k ∧ 0 < S k ω}
  have hE_all_meas : MeasurableSet E_all := by
    have heq : E_all = ⋃ N : ℕ, E N := by
      ext ω
      simp only [E_all, E, Set.mem_ofPred_eq, Set.mem_iUnion]
      exact ⟨fun ⟨k, hk1, hpos⟩ => ⟨k, k, hk1, le_rfl, hpos⟩,
        fun ⟨_, k, hk1, _, hpos⟩ => ⟨k, hk1, hpos⟩⟩
    rw [heq]
    exact MeasurableSet.iUnion hE_meas
  have hlim : Tendsto (fun N => ∫ ω, (E N).indicator f ω ∂P) atTop
      (nhds (∫ ω, E_all.indicator f ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => ‖f ω‖)
      (fun N => hf.aestronglyMeasurable.indicator (hE_meas N))
      hf.norm
      (fun N => Eventually.of_forall fun ω => by
        by_cases h : ω ∈ E N <;> simp [h])
      (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ E_all
    · rcases hω with ⟨k, hk1, hpos⟩
      refine tendsto_atTop_of_eventually_const (i₀ := k) fun N hN => ?_
      have hmem : ω ∈ E N := ⟨k, hk1, hN, hpos⟩
      have hmem_all : ω ∈ E_all := ⟨k, hk1, hpos⟩
      simp [hmem, hmem_all]
    · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun N _ => ?_
      have hnmem : ω ∉ E N := fun ⟨k, hk1, _, hpos⟩ => hω ⟨k, hk1, hpos⟩
      simp [hnmem, hω]
  have hlim' : Tendsto (fun N => ∫ ω in E N, f ω ∂P) atTop
      (nhds (∫ ω in E_all, f ω ∂P)) := by
    simpa only [integral_indicator (hE_meas _), integral_indicator hE_all_meas] using hlim
  exact ge_of_tendsto' hlim' hstep

private lemma flowMeasure_limsup_le_ae {θ : Flow Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (herg : IsErgodicFlow θ P)
    {m : ℝ → ℝ → Ω → ℝ} (hm : IsFlowMeasure θ m)
    (hmint : Integrable (m 0 1) P)
    {c : ℝ} (hc : ∫ ω, m 0 1 ω ∂P < c) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n →
      m (-(n : ℝ)) 0 ω / (n : ℝ) ≤ c + 1 / ((k : ℝ) + 1) := by
  let B : Set Ω := {ω | ∃ k : ℕ, ∀ N : ℕ, ∃ n : ℕ, (N ≤ n ∧ 1 ≤ n) ∧
    c + 1 / ((k : ℝ) + 1) < m (-(n : ℝ)) 0 ω / (n : ℝ)}
  have hB_meas : MeasurableSet B := by
    have heq : B = ⋃ k : ℕ, ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n ∧ 1 ≤ n),
        {ω | c + 1 / ((k : ℝ) + 1) < m (-(n : ℝ)) 0 ω / (n : ℝ)} := by
      ext ω
      simp [B]
    rw [heq]
    refine MeasurableSet.iUnion fun k => MeasurableSet.iInter fun N =>
      MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => ?_
    exact measurableSet_lt measurable_const ((hm.2.2.2 (-(n : ℝ)) 0).div_const (n : ℝ))
  have hB_inv_sub : ∀ (t : ℝ) (ω : Ω), ω ∈ B → θ t ω ∈ B := by
    intro t ω ⟨k, hk⟩
    refine ⟨2 * k + 2, fun N => ?_⟩
    let a : ℤ := ⌊t⌋
    let b : ℤ := ⌈t⌉
    have ha : (a : ℝ) ≤ t := Int.floor_le t
    have hb : t ≤ (b : ℝ) := Int.le_ceil t
    let C_const : ℝ := if 0 ≤ (a : ℝ) then 0 else -m (a : ℝ) 0 ω
    have hC_bound : ∀ n : ℕ, (-(n : ℝ) ≤ (a : ℝ)) →
        m (-(n : ℝ)) 0 ω + C_const ≤ m (-(n : ℝ)) (a : ℝ) ω := by
      intro n hna
      by_cases ha0 : 0 ≤ (a : ℝ)
      · simp only [C_const, ha0, ↓reduceIte, add_zero]
        exact flowMeasure_mono_right hm (by linarith) ha0 ω
      · simp only [C_const, ha0, ↓reduceIte]
        have ha0' : (a : ℝ) ≤ 0 := le_of_not_ge ha0
        have hadd := hm.2.1 (-(n : ℝ)) (a : ℝ) 0 ω hna ha0'
        linarith
    let ε : ℝ := 1 / ((k : ℝ) + 1) - 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)
    have hε : 0 < ε := by
      dsimp only [ε]
      push_cast
      have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h2 : (k : ℝ) + 1 < 2 * (k : ℝ) + 2 + 1 := by linarith
      exact sub_pos.mpr (one_div_lt_one_div_of_lt h1 h2)
    obtain ⟨M₀, hM₀⟩ := exists_nat_gt (max (max ((N : ℝ) + |(b : ℝ)| + 1) (|(a : ℝ)| + 1))
      (((|c| + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * |(b : ℝ)| + |C_const| + 1) / ε))
    obtain ⟨n, ⟨hnM₀, hn1⟩, hlt⟩ := hk M₀
    have hn_gt : ((N : ℝ) + |(b : ℝ)| + 1) < (n : ℝ) :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _))
        (lt_of_lt_of_le hM₀ (Nat.cast_le.mpr hnM₀))
    have hna_gt : |(a : ℝ)| + 1 < (n : ℝ) :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _))
        (lt_of_lt_of_le hM₀ (Nat.cast_le.mpr hnM₀))
    have hneps_gt : ((|c| + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * |(b : ℝ)| + |C_const| + 1) / ε < (n : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hM₀ (Nat.cast_le.mpr hnM₀))
    let n' : ℕ := (n + b).toNat
    have hnb_nonneg : (0 : ℤ) ≤ (n : ℤ) + b := by
      have : -(b : ℝ) ≤ |(b : ℝ)| := neg_le_abs _
      have : (0 : ℝ) ≤ (n : ℝ) + (b : ℝ) := by linarith
      exact_mod_cast this
    have hn'_cast : (n' : ℝ) = (n : ℝ) + (b : ℝ) := by
      have : (n' : ℤ) = (n : ℤ) + b := Int.toNat_of_nonneg hnb_nonneg
      exact_mod_cast this
    have hn'_ge_N : N ≤ n' := by
      have : (N : ℝ) ≤ (n' : ℝ) := by
        rw [hn'_cast]
        have : -(b : ℝ) ≤ |(b : ℝ)| := neg_le_abs _
        linarith
      exact_mod_cast this
    have hn'_ge_1 : 1 ≤ n' := by
      have : (1 : ℝ) ≤ (n' : ℝ) := by
        rw [hn'_cast]
        have : -(b : ℝ) ≤ |(b : ℝ)| := neg_le_abs _
        linarith
      exact_mod_cast this
    refine ⟨n', ⟨hn'_ge_N, hn'_ge_1⟩, ?_⟩
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hn'_pos : (0 : ℝ) < (n' : ℝ) := by positivity
    have hna : -(n : ℝ) ≤ (a : ℝ) := by
      have : -(a : ℝ) ≤ |(a : ℝ)| := neg_le_abs _
      linarith
    have hshift : m (-(n' : ℝ)) 0 (θ t ω) = m (-(n' : ℝ) + t) t ω := by
      rw [flowMeasure_shift hm (by linarith : -(n' : ℝ) ≤ 0)]
      ring_nf
    have hmono : m (-(n : ℝ)) (a : ℝ) ω ≤ m (-(n' : ℝ) + t) t ω := by
      have h1 : -(n' : ℝ) + t ≤ -(n : ℝ) := by rw [hn'_cast]; linarith
      have h2 : -(n : ℝ) ≤ (a : ℝ) := hna
      have h3 : (a : ℝ) ≤ t := ha
      exact (flowMeasure_mono_left hm h1 h2 ω).trans (flowMeasure_mono_right hm (h1.trans h2) h3 ω)
    have hbound1 : m (-(n : ℝ)) 0 ω + C_const ≤ m (-(n' : ℝ)) 0 (θ t ω) := by
      rw [hshift]
      exact (hC_bound n hna).trans hmono
    have hbound2 : (c + 1 / ((k : ℝ) + 1)) * (n : ℝ) < m (-(n : ℝ)) 0 ω :=
      (lt_div_iff₀ hn_pos).mp hlt
    rw [lt_div_iff₀ hn'_pos]
    have hεn : (|c| + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * |(b : ℝ)| + |C_const| + 1 < (n : ℝ) * ε :=
      (div_lt_iff₀ hε).mp hneps_gt
    have hc_mul : (c + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * (b : ℝ) ≤
        (|c| + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * |(b : ℝ)| := by
      have hpos_frac : (0 : ℝ) < 1 / ((2 * k + 2 : ℕ) + 1 : ℝ) := by positivity
      calc (c + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * (b : ℝ)
          ≤ |c + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)| * |(b : ℝ)| := by
            rw [← abs_mul]; exact le_abs_self _
        _ ≤ (|c| + |1 / ((2 * k + 2 : ℕ) + 1 : ℝ)|) * |(b : ℝ)| := by
            gcongr; exact abs_add_le _ _
        _ = (|c| + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * |(b : ℝ)| := by
            rw [abs_of_pos hpos_frac]
    have hC_neg : -C_const ≤ |C_const| := neg_le_abs _
    rw [hn'_cast] at hbound1 ⊢
    have hmul : (c + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * ((n : ℝ) + (b : ℝ)) =
        (c + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * (n : ℝ) +
        (c + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * (b : ℝ) := mul_add _ _ _
    have hε_def : (c + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * (n : ℝ) + (n : ℝ) * ε =
        (c + 1 / ((k : ℝ) + 1)) * (n : ℝ) := by
      dsimp only [ε]; push_cast; ring
    linarith
  have hB_inv : ∀ t : ℝ, θ t ⁻¹' B = B := by
    intro t
    ext ω
    constructor
    · intro hω
      have h := hB_inv_sub (-t) (θ t ω) hω
      have h0 : θ (-t) (θ t ω) = ω := by
        have hadd : θ (-t + t) ω = θ (-t) (θ t ω) := congrFun (θ.map_add (-t) t) ω
        rw [← hadd, neg_add_cancel, θ.map_zero]
        rfl
      rwa [h0] at h
    · exact hB_inv_sub t ω
  have hPB : P B = 0 ∨ P B = 1 := herg.2 B hB_meas hB_inv
  have hPB_zero : P B = 0 := by
    rcases hPB with h0 | h1
    · exact h0
    · exfalso
      let T := θ (-1)
      have hT : MeasurePreserving T P P := ⟨θ.measurable' (-1), herg.1 (-1)⟩
      have hm1_eq : m (-1) 0 = fun ω => m 0 1 (T ω) := by
        ext ω
        rw [hm.2.2.1 (-1) 0 ω (by norm_num)]
        norm_num [T]
      have hm1_int : Integrable (m (-1) 0) P := by
        rw [hm1_eq]
        exact hT.integrable_comp_of_integrable hmint
      let f : Ω → ℝ := fun ω => m (-1) 0 ω - c
      have hf_meas : Measurable f := (hm.2.2.2 (-1) 0).sub measurable_const
      have hf_int : Integrable f P := hm1_int.sub (integrable_const c)
      let E : Set Ω := {ω | ∃ k : ℕ, 1 ≤ k ∧ 0 < birkhoffSum T f k ω}
      have hBE : B ⊆ E := by
        intro ω ⟨k, hk⟩
        obtain ⟨n, ⟨_, hn1⟩, hlt⟩ := hk 1
        refine ⟨n, hn1, ?_⟩
        have hsum : birkhoffSum T f n ω = m (-(n : ℝ)) 0 ω - (n : ℝ) * c := by
          have : birkhoffSum T f n ω = birkhoffSum T (m (-1) 0) n ω - birkhoffSum T (fun _ => c) n ω :=
            birkhoffSum_sub T (m (-1) 0) (fun _ => c) n ω
          rw [this, birkhoffSum_flowMeasure hm]
          simp [birkhoffSum, Finset.sum_const, nsmul_eq_mul]
        rw [hsum]
        have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
        have h1 : (c + 1 / ((k : ℝ) + 1)) * (n : ℝ) < m (-(n : ℝ)) 0 ω :=
          (lt_div_iff₀ hn_pos).mp hlt
        have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) * (n : ℝ) := by positivity
        linarith
      have hE_ae : E =ᵐ[P] Set.univ := by
        have hBc : P Bᶜ = 0 := by
          rw [prob_compl_eq_zero_iff hB_meas]
          exact h1
        have hEc : P Eᶜ = 0 := measure_mono_null (Set.compl_subset_compl.mpr hBE) hBc
        exact ae_eq_univ.mpr hEc
      have hmax := maximal_ergodic_theorem hT hf_meas hf_int
      have hint_eq : ∫ ω in E, f ω ∂P = ∫ ω, f ω ∂P := by
        rw [setIntegral_congr_set hE_ae, setIntegral_univ]
      rw [hint_eq] at hmax
      have hint_comp : ∫ ω, m 0 1 (T ω) ∂P = ∫ ω, m 0 1 ω ∂P := by
        have hm_aesm : AEStronglyMeasurable (m 0 1) (Measure.map T P) := by
          rw [hT.map_eq]; exact hmint.aestronglyMeasurable
        have := integral_map hT.measurable.aemeasurable hm_aesm
        rw [hT.map_eq] at this
        exact this.symm
      have hint_f : ∫ ω, f ω ∂P = (∫ ω, m 0 1 ω ∂P) - c := by
        dsimp only [f]
        rw [integral_sub hm1_int (integrable_const c), integral_const, probReal_univ, one_smul,
          hm1_eq, hint_comp]
      linarith
  have hB_ae : ∀ᵐ ω ∂P, ω ∉ B := by
    rw [ae_iff]
    simpa [not_not] using hPB_zero
  filter_upwards [hB_ae] with ω hω k
  simp only [B, Set.mem_ofPred_eq, not_exists, not_forall, not_and, not_lt] at hω
  obtain ⟨N, hN⟩ := hω k
  exact ⟨N, fun n hnN hn1 => hN n ⟨hnN, hn1⟩⟩

private lemma flowMeasure_liminf_ge_ae {θ : Flow Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (herg : IsErgodicFlow θ P)
    {m : ℝ → ℝ → Ω → ℝ} (hm : IsFlowMeasure θ m)
    (hmint : Integrable (m 0 1) P)
    {d : ℝ} (hd : d < ∫ ω, m 0 1 ω ∂P) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n →
      d - 1 / ((k : ℝ) + 1) ≤ m (-(n : ℝ)) 0 ω / (n : ℝ) := by
  let B : Set Ω := {ω | ∃ k : ℕ, ∀ N : ℕ, ∃ n : ℕ, (N ≤ n ∧ 1 ≤ n) ∧
    m (-(n : ℝ)) 0 ω / (n : ℝ) < d - 1 / ((k : ℝ) + 1)}
  have hB_meas : MeasurableSet B := by
    have heq : B = ⋃ k : ℕ, ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n ∧ 1 ≤ n),
        {ω | m (-(n : ℝ)) 0 ω / (n : ℝ) < d - 1 / ((k : ℝ) + 1)} := by
      ext ω
      simp [B]
    rw [heq]
    refine MeasurableSet.iUnion fun k => MeasurableSet.iInter fun N =>
      MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => ?_
    exact measurableSet_lt ((hm.2.2.2 (-(n : ℝ)) 0).div_const (n : ℝ)) measurable_const
  have hB_inv_sub : ∀ (t : ℝ) (ω : Ω), ω ∈ B → θ t ω ∈ B := by
    intro t ω ⟨k, hk⟩
    refine ⟨2 * k + 2, fun N => ?_⟩
    let a : ℤ := ⌊t⌋
    let b : ℤ := ⌈t⌉
    have ha : (a : ℝ) ≤ t := Int.floor_le t
    have hb : t ≤ (b : ℝ) := Int.le_ceil t
    let C_const : ℝ := if 0 ≤ (b : ℝ) then m 0 (b : ℝ) ω else 0
    have hC_bound : ∀ n : ℕ, (-(n : ℝ) ≤ (b : ℝ)) →
        m (-(n : ℝ)) (b : ℝ) ω ≤ m (-(n : ℝ)) 0 ω + C_const := by
      intro n hnb
      by_cases hb0 : 0 ≤ (b : ℝ)
      · simp only [C_const, hb0, ↓reduceIte]
        have hadd := hm.2.1 (-(n : ℝ)) 0 (b : ℝ) ω (by linarith) hb0
        linarith
      · simp only [C_const, hb0, ↓reduceIte, add_zero]
        have hb0' : (b : ℝ) ≤ 0 := le_of_not_ge hb0
        exact flowMeasure_mono_right hm hnb hb0' ω
    let ε : ℝ := 1 / ((k : ℝ) + 1) - 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)
    have hε : 0 < ε := by
      dsimp only [ε]
      push_cast
      have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h2 : (k : ℝ) + 1 < 2 * (k : ℝ) + 2 + 1 := by linarith
      exact sub_pos.mpr (one_div_lt_one_div_of_lt h1 h2)
    obtain ⟨M₀, hM₀⟩ := exists_nat_gt (max (max ((N : ℝ) + |(a : ℝ)| + 1) (|(b : ℝ)| + 1))
      (((|d| + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * |(a : ℝ)| + |C_const| + 1) / ε))
    obtain ⟨n, ⟨hnM₀, hn1⟩, hlt⟩ := hk M₀
    have hn_gt : ((N : ℝ) + |(a : ℝ)| + 1) < (n : ℝ) :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _))
        (lt_of_lt_of_le hM₀ (Nat.cast_le.mpr hnM₀))
    have hnb_gt : |(b : ℝ)| + 1 < (n : ℝ) :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _))
        (lt_of_lt_of_le hM₀ (Nat.cast_le.mpr hnM₀))
    have hneps_gt : ((|d| + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * |(a : ℝ)| + |C_const| + 1) / ε < (n : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hM₀ (Nat.cast_le.mpr hnM₀))
    let n' : ℕ := (n + a).toNat
    have hna_nonneg : (0 : ℤ) ≤ (n : ℤ) + a := by
      have : -(a : ℝ) ≤ |(a : ℝ)| := neg_le_abs _
      have : (0 : ℝ) ≤ (n : ℝ) + (a : ℝ) := by linarith
      exact_mod_cast this
    have hn'_cast : (n' : ℝ) = (n : ℝ) + (a : ℝ) := by
      have : (n' : ℤ) = (n : ℤ) + a := Int.toNat_of_nonneg hna_nonneg
      exact_mod_cast this
    have hn'_ge_N : N ≤ n' := by
      have : (N : ℝ) ≤ (n' : ℝ) := by
        rw [hn'_cast]
        have : -(a : ℝ) ≤ |(a : ℝ)| := neg_le_abs _
        linarith
      exact_mod_cast this
    have hn'_ge_1 : 1 ≤ n' := by
      have : (1 : ℝ) ≤ (n' : ℝ) := by
        rw [hn'_cast]
        have : -(a : ℝ) ≤ |(a : ℝ)| := neg_le_abs _
        linarith
      exact_mod_cast this
    refine ⟨n', ⟨hn'_ge_N, hn'_ge_1⟩, ?_⟩
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hn'_pos : (0 : ℝ) < (n' : ℝ) := by positivity
    have hnb : -(n : ℝ) ≤ (b : ℝ) := by
      have : -(b : ℝ) ≤ |(b : ℝ)| := neg_le_abs _
      linarith
    have hshift : m (-(n' : ℝ)) 0 (θ t ω) = m (-(n' : ℝ) + t) t ω := by
      rw [flowMeasure_shift hm (by linarith : -(n' : ℝ) ≤ 0)]
      ring_nf
    have hmono : m (-(n' : ℝ) + t) t ω ≤ m (-(n : ℝ)) (b : ℝ) ω := by
      have h1 : -(n : ℝ) ≤ -(n' : ℝ) + t := by rw [hn'_cast]; linarith
      have h2 : -(n' : ℝ) + t ≤ t := by linarith
      have h3 : t ≤ (b : ℝ) := hb
      exact (flowMeasure_mono_left hm h1 h2 ω).trans (flowMeasure_mono_right hm (h1.trans h2) h3 ω)
    have hbound1 : m (-(n' : ℝ)) 0 (θ t ω) ≤ m (-(n : ℝ)) 0 ω + C_const := by
      rw [hshift]
      exact hmono.trans (hC_bound n hnb)
    have hbound2 : m (-(n : ℝ)) 0 ω < (d - 1 / ((k : ℝ) + 1)) * (n : ℝ) :=
      (div_lt_iff₀ hn_pos).mp hlt
    rw [div_lt_iff₀ hn'_pos]
    have hεn : (|d| + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * |(a : ℝ)| + |C_const| + 1 < (n : ℝ) * ε :=
      (div_lt_iff₀ hε).mp hneps_gt
    have hd_mul : -((d - 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * (a : ℝ)) ≤
        (|d| + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * |(a : ℝ)| := by
      have hpos_frac : (0 : ℝ) < 1 / ((2 * k + 2 : ℕ) + 1 : ℝ) := by positivity
      calc -((d - 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * (a : ℝ))
          ≤ |(d - 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * (a : ℝ)| := neg_le_abs _
        _ = |d - 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)| * |(a : ℝ)| := abs_mul _ _
        _ ≤ (|d| + |1 / ((2 * k + 2 : ℕ) + 1 : ℝ)|) * |(a : ℝ)| := by
            gcongr; exact abs_sub _ _
        _ = (|d| + 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * |(a : ℝ)| := by
            rw [abs_of_pos hpos_frac]
    have hC_pos : C_const ≤ |C_const| := le_abs_self _
    rw [hn'_cast] at hbound1 ⊢
    have hmul : (d - 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * ((n : ℝ) + (a : ℝ)) =
        (d - 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * (n : ℝ) +
        (d - 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * (a : ℝ) := mul_add _ _ _
    have hε_def : (d - 1 / ((k : ℝ) + 1)) * (n : ℝ) + (n : ℝ) * ε =
        (d - 1 / ((2 * k + 2 : ℕ) + 1 : ℝ)) * (n : ℝ) := by
      dsimp only [ε]; push_cast; ring
    linarith
  have hB_inv : ∀ t : ℝ, θ t ⁻¹' B = B := by
    intro t
    ext ω
    constructor
    · intro hω
      have h := hB_inv_sub (-t) (θ t ω) hω
      have h0 : θ (-t) (θ t ω) = ω := by
        have hadd : θ (-t + t) ω = θ (-t) (θ t ω) := congrFun (θ.map_add (-t) t) ω
        rw [← hadd, neg_add_cancel, θ.map_zero]
        rfl
      rwa [h0] at h
    · exact hB_inv_sub t ω
  have hPB : P B = 0 ∨ P B = 1 := herg.2 B hB_meas hB_inv
  have hPB_zero : P B = 0 := by
    rcases hPB with h0 | h1
    · exact h0
    · exfalso
      let T := θ (-1)
      have hT : MeasurePreserving T P P := ⟨θ.measurable' (-1), herg.1 (-1)⟩
      have hm1_eq : m (-1) 0 = fun ω => m 0 1 (T ω) := by
        ext ω
        rw [hm.2.2.1 (-1) 0 ω (by norm_num)]
        norm_num [T]
      have hm1_int : Integrable (m (-1) 0) P := by
        rw [hm1_eq]
        exact hT.integrable_comp_of_integrable hmint
      let f : Ω → ℝ := fun ω => d - m (-1) 0 ω
      have hf_meas : Measurable f := measurable_const.sub (hm.2.2.2 (-1) 0)
      have hf_int : Integrable f P := (integrable_const d).sub hm1_int
      let E : Set Ω := {ω | ∃ k : ℕ, 1 ≤ k ∧ 0 < birkhoffSum T f k ω}
      have hBE : B ⊆ E := by
        intro ω ⟨k, hk⟩
        obtain ⟨n, ⟨_, hn1⟩, hlt⟩ := hk 1
        refine ⟨n, hn1, ?_⟩
        have hsum : birkhoffSum T f n ω = (n : ℝ) * d - m (-(n : ℝ)) 0 ω := by
          have : birkhoffSum T f n ω = birkhoffSum T (fun _ => d) n ω - birkhoffSum T (m (-1) 0) n ω :=
            birkhoffSum_sub T (fun _ => d) (m (-1) 0) n ω
          rw [this, birkhoffSum_flowMeasure hm]
          simp [birkhoffSum, Finset.sum_const, nsmul_eq_mul]
        rw [hsum]
        have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
        have h1 : m (-(n : ℝ)) 0 ω < (d - 1 / ((k : ℝ) + 1)) * (n : ℝ) :=
          (div_lt_iff₀ hn_pos).mp hlt
        have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) * (n : ℝ) := by positivity
        linarith
      have hE_ae : E =ᵐ[P] Set.univ := by
        have hBc : P Bᶜ = 0 := by
          rw [prob_compl_eq_zero_iff hB_meas]
          exact h1
        have hEc : P Eᶜ = 0 := measure_mono_null (Set.compl_subset_compl.mpr hBE) hBc
        exact ae_eq_univ.mpr hEc
      have hmax := maximal_ergodic_theorem hT hf_meas hf_int
      have hint_eq : ∫ ω in E, f ω ∂P = ∫ ω, f ω ∂P := by
        rw [setIntegral_congr_set hE_ae, setIntegral_univ]
      rw [hint_eq] at hmax
      have hint_comp : ∫ ω, m 0 1 (T ω) ∂P = ∫ ω, m 0 1 ω ∂P := by
        have hm_aesm : AEStronglyMeasurable (m 0 1) (Measure.map T P) := by
          rw [hT.map_eq]; exact hmint.aestronglyMeasurable
        have := integral_map hT.measurable.aemeasurable hm_aesm
        rw [hT.map_eq] at this
        exact this.symm
      have hint_f : ∫ ω, f ω ∂P = d - ∫ ω, m 0 1 ω ∂P := by
        dsimp only [f]
        rw [integral_sub (integrable_const d) hm1_int, integral_const, probReal_univ, one_smul,
          hm1_eq, hint_comp]
      linarith
  have hB_ae : ∀ᵐ ω ∂P, ω ∉ B := by
    rw [ae_iff]
    simpa [not_not] using hPB_zero
  filter_upwards [hB_ae] with ω hω k
  simp only [B, Set.mem_ofPred_eq, not_exists, not_forall, not_and, not_lt] at hω
  obtain ⟨N, hN⟩ := hω k
  exact ⟨N, fun n hnN hn1 => hN n ⟨hnN, hn1⟩⟩

private lemma fluidLoynesSet_nonempty {θ : Flow Ω} {A C : ℝ → ℝ → Ω → ℝ}
    (hA : IsFlowMeasure θ A) (hC : IsFlowMeasure θ C) (t : ℝ) (ω : Ω) :
    (fluidLoynesSet A C t ω).Nonempty :=
  ⟨0, t, le_rfl, by simp [flowMeasure_self hA, flowMeasure_self hC]⟩

private lemma fluidLoynesSet_shift {θ : Flow Ω} {A C : ℝ → ℝ → Ω → ℝ}
    (hA : IsFlowMeasure θ A) (hC : IsFlowMeasure θ C) (t s : ℝ) (ω : Ω) :
    fluidLoynesSet A C t (θ s ω) = fluidLoynesSet A C (t + s) ω := by
  ext x
  simp only [fluidLoynesSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u, hut, rfl⟩
    exact ⟨u + s, by linarith, by rw [flowMeasure_shift hA hut, flowMeasure_shift hC hut]⟩
  · rintro ⟨v, hvt, rfl⟩
    refine ⟨v - s, by linarith, ?_⟩
    rw [flowMeasure_shift hA (by linarith : v - s ≤ t),
      flowMeasure_shift hC (by linarith : v - s ≤ t)]
    ring_nf

private lemma bddAbove_fluidLoynesSet_all {θ : Flow Ω} {A C : ℝ → ℝ → Ω → ℝ}
    (hA : IsFlowMeasure θ A) (hC : IsFlowMeasure θ C) {ω : Ω}
    (h0 : BddAbove (fluidLoynesSet A C 0 ω)) (t : ℝ) :
    BddAbove (fluidLoynesSet A C t ω) := by
  rcases h0 with ⟨M, hM⟩
  by_cases ht : 0 ≤ t
  · refine ⟨max (M + A 0 t ω - C 0 t ω) (A 0 t ω), ?_⟩
    rintro x ⟨u, hut, rfl⟩
    by_cases hu : u ≤ 0
    · have huM : A u 0 ω - C u 0 ω ≤ M := hM ⟨u, hu, rfl⟩
      rw [hA.2.1 u 0 t ω hu ht, hC.2.1 u 0 t ω hu ht]
      exact le_trans (by linarith) (le_max_left _ _)
    · have hu0 : 0 ≤ u := le_of_not_ge hu
      have hA_le : A u t ω ≤ A 0 t ω := flowMeasure_mono_left hA hu0 hut ω
      have hC_nn : 0 ≤ C u t ω := hC.1 u t ω hut
      exact le_trans (by linarith) (le_max_right _ _)
  · have ht0 : t ≤ 0 := le_of_not_ge ht
    refine ⟨M - (A t 0 ω - C t 0 ω), ?_⟩
    rintro x ⟨u, hut, rfl⟩
    have hu0 : u ≤ 0 := hut.trans ht0
    have huM : A u 0 ω - C u 0 ω ≤ M := hM ⟨u, hu0, rfl⟩
    rw [hA.2.1 u t 0 ω hut ht0, hC.2.1 u t 0 ω hut ht0] at huM
    linarith

private lemma isFluidWorkloadPath_of_bddAbove {θ : Flow Ω} {A C : ℝ → ℝ → Ω → ℝ}
    (hA : IsFlowMeasure θ A) (hC : IsFlowMeasure θ C) {ω : Ω}
    (h0 : BddAbove (fluidLoynesSet A C 0 ω)) :
    IsFluidWorkloadPath A C (fun t ω => sSup (fluidLoynesSet A C t ω)) ω := by
  intro s t hst
  let S₁ : Set ℝ := {x | ∃ u : ℝ, u ≤ s ∧ x = A u t ω - C u t ω}
  let S₂ : Set ℝ := {x | ∃ u : ℝ, s ≤ u ∧ u ≤ t ∧ x = A u t ω - C u t ω}
  have hunion : fluidLoynesSet A C t ω = S₁ ∪ S₂ := by
    ext x
    simp only [fluidLoynesSet, S₁, S₂, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hut, rfl⟩
      by_cases hus : u ≤ s
      · exact Or.inl ⟨u, hus, rfl⟩
      · exact Or.inr ⟨u, le_of_not_ge hus, hut, rfl⟩
    · rintro (⟨u, hus, rfl⟩ | ⟨u, _, hut, rfl⟩)
      · exact ⟨u, hus.trans hst, rfl⟩
      · exact ⟨u, hut, rfl⟩
  have hbdd_t : BddAbove (fluidLoynesSet A C t ω) := bddAbove_fluidLoynesSet_all hA hC h0 t
  have hbdd_s : BddAbove (fluidLoynesSet A C s ω) := bddAbove_fluidLoynesSet_all hA hC h0 s
  have hne₁ : S₁.Nonempty := ⟨A s t ω - C s t ω, s, le_rfl, rfl⟩
  have hne₂ : S₂.Nonempty := ⟨0, t, hst, le_rfl, by simp [flowMeasure_self hA, flowMeasure_self hC]⟩
  have hbdd₁ : BddAbove S₁ := hbdd_t.mono (by rw [hunion]; exact Set.subset_union_left)
  have hbdd₂ : BddAbove S₂ := hbdd_t.mono (by rw [hunion]; exact Set.subset_union_right)
  have hS₁_eq : sSup S₁ = sSup (fluidLoynesSet A C s ω) + A s t ω - C s t ω := by
    have hS₁_img : S₁ = (fun y => y + (A s t ω - C s t ω)) '' fluidLoynesSet A C s ω := by
      ext x
      simp only [S₁, fluidLoynesSet, Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨u, hus, rfl⟩
        refine ⟨A u s ω - C u s ω, ⟨u, hus, rfl⟩, ?_⟩
        rw [hA.2.1 u s t ω hus hst, hC.2.1 u s t ω hus hst]
        ring
      · rintro ⟨y, ⟨u, hus, rfl⟩, rfl⟩
        refine ⟨u, hus, ?_⟩
        rw [hA.2.1 u s t ω hus hst, hC.2.1 u s t ω hus hst]
        ring
    rw [hS₁_img]
    have hne_s := fluidLoynesSet_nonempty hA hC s ω
    have hadd_sup : sSup ((fun y => y + (A s t ω - C s t ω)) '' fluidLoynesSet A C s ω) =
        sSup (fluidLoynesSet A C s ω) + (A s t ω - C s t ω) := by
      apply le_antisymm
      · refine csSup_le (hne_s.image _) ?_
        rintro _ ⟨y, hy, rfl⟩
        linarith [le_csSup hbdd_s hy]
      · have hle : sSup (fluidLoynesSet A C s ω) ≤
            sSup ((fun y => y + (A s t ω - C s t ω)) '' fluidLoynesSet A C s ω) - (A s t ω - C s t ω) := by
          refine csSup_le hne_s fun y hy => ?_
          have hmem : y + (A s t ω - C s t ω) ∈
              (fun y => y + (A s t ω - C s t ω)) '' fluidLoynesSet A C s ω := ⟨y, hy, rfl⟩
          have hbdd_img : BddAbove ((fun y => y + (A s t ω - C s t ω)) '' fluidLoynesSet A C s ω) := by
            rw [← hS₁_img]; exact hbdd₁
          linarith [le_csSup hbdd_img hmem]
        linarith
    linarith
  dsimp only
  rw [hunion, csSup_union hbdd₁ hne₁ hbdd₂ hne₂, hS₁_eq]

private lemma minimal_of_isFluidWorkloadPath {θ : Flow Ω} {A C : ℝ → ℝ → Ω → ℝ}
    (hA : IsFlowMeasure θ A) (hC : IsFlowMeasure θ C) {W' : ℝ → Ω → ℝ} {ω : Ω}
    (h0 : BddAbove (fluidLoynesSet A C 0 ω)) (hW' : IsFluidWorkloadPath A C W' ω) (t : ℝ) :
    sSup (fluidLoynesSet A C t ω) ≤ W' t ω := by
  refine csSup_le (fluidLoynesSet_nonempty hA hC t ω) ?_
  rintro x ⟨u, hut, rfl⟩
  have heq := hW' u t hut
  have hle1 : sSup {y | ∃ v : ℝ, u ≤ v ∧ v ≤ t ∧ y = A v t ω - C v t ω} ≤ W' t ω := by
    rw [heq]; exact le_max_right _ _
  have hsub : {y | ∃ v : ℝ, u ≤ v ∧ v ≤ t ∧ y = A v t ω - C v t ω} ⊆ fluidLoynesSet A C t ω := by
    rintro y ⟨v, _, hvt, rfl⟩
    exact ⟨v, hvt, rfl⟩
  have hbdd : BddAbove {y | ∃ v : ℝ, u ≤ v ∧ v ≤ t ∧ y = A v t ω - C v t ω} :=
    (bddAbove_fluidLoynesSet_all hA hC h0 t).mono hsub
  have hmem : A u t ω - C u t ω ∈ {y | ∃ v : ℝ, u ≤ v ∧ v ≤ t ∧ y = A v t ω - C v t ω} :=
    ⟨u, le_rfl, hut, rfl⟩
  exact (le_csSup hbdd hmem).trans hle1

end Helpers

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (θ : Flow Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (herg : IsErgodicFlow θ P)
    (A C : ℝ → ℝ → Ω → ℝ) (hA : IsFlowMeasure θ A) (hC : IsFlowMeasure θ C)
    (lam mu : ℝ)
    (hAint : Integrable (A 0 1) P) (hCint : Integrable (C 0 1) P)
    (hlam : 0 < lam ∧ lam = ∫ ω, A 0 1 ω ∂P)
    (hmu : 0 < mu ∧ mu = ∫ ω, C 0 1 ω ∂P)
    (hstab : lam < mu) :
    ∃ W : ℝ → Ω → ℝ,
      IsCompatible θ W ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ,
        BddAbove (fluidLoynesSet A C t ω) ∧ W t ω = sSup (fluidLoynesSet A C t ω)) ∧
      (∀ᵐ ω ∂P, IsFluidWorkloadPath A C W ω) ∧
      (∀ W' : ℝ → Ω → ℝ, IsCompatible θ W' → (∀ᵐ ω ∂P, IsFluidWorkloadPath A C W' ω) →
        ∀ᵐ ω ∂P, ∀ t : ℝ, W t ω ≤ W' t ω) := by
  let W : ℝ → Ω → ℝ := fun t ω => sSup (fluidLoynesSet A C t ω)
  have hcompat : IsCompatible θ W := by
    intro t s ω
    simp only [W, fluidLoynesSet_shift hA hC]
  have hbdd0_ae : ∀ᵐ ω ∂P, BddAbove (fluidLoynesSet A C 0 ω) := by
    let c : ℝ := (2 * lam + mu) / 3
    let d : ℝ := (lam + 2 * mu) / 3
    have hc : ∫ ω, A 0 1 ω ∂P < c := by rw [← hlam.2]; dsimp only [c]; linarith
    have hd : d < ∫ ω, C 0 1 ω ∂P := by rw [← hmu.2]; dsimp only [d]; linarith
    have hA_ae := flowMeasure_limsup_le_ae herg hA hAint hc
    have hC_ae := flowMeasure_liminf_ge_ae herg hC hCint hd
    filter_upwards [hA_ae, hC_ae] with ω hωA hωC
    obtain ⟨k, hk⟩ := exists_nat_gt (3 / (d - c))
    have hdc : 0 < d - c := by dsimp only [c, d]; linarith
    have hk_inv : 1 / ((k : ℝ) + 1) < (d - c) / 3 := by
      have hk1 : 3 / (d - c) < (k : ℝ) + 1 := lt_trans hk (by linarith)
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
      have h2 := (div_lt_iff₀ hdc).mp hk1
      linarith
    obtain ⟨N₁, hN₁⟩ := hωA k
    obtain ⟨N₂, hN₂⟩ := hωC k
    let c' : ℝ := c + 1 / ((k : ℝ) + 1)
    let d' : ℝ := d - 1 / ((k : ℝ) + 1)
    have hcd' : 0 < d' - c' := by dsimp only [c', d']; linarith
    obtain ⟨N₃, hN₃⟩ := exists_nat_gt (max (max (N₁ : ℝ) (N₂ : ℝ)) (max 1 (c' / (d' - c'))))
    have hN₃_1 : N₁ ≤ N₃ := by
      have : (N₁ : ℝ) < (N₃ : ℝ) := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN₃
      exact Nat.le_of_lt (by exact_mod_cast this)
    have hN₃_2 : N₂ ≤ N₃ := by
      have : (N₂ : ℝ) < (N₃ : ℝ) := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN₃
      exact Nat.le_of_lt (by exact_mod_cast this)
    have hN₃_pos : 1 ≤ N₃ := by
      have : (1 : ℝ) < (N₃ : ℝ) := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN₃
      exact Nat.le_of_lt (by exact_mod_cast this)
    have hN₃_c : c' / (d' - c') < (N₃ : ℝ) :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN₃
    refine ⟨A (-(N₃ : ℝ)) 0 ω, ?_⟩
    rintro x ⟨u, hu0, rfl⟩
    let n : ℕ := ⌊-u⌋₊
    have hn_le : (n : ℝ) ≤ -u := Nat.floor_le (by linarith)
    have hlt_n1 : -u < (n : ℝ) + 1 := Nat.lt_floor_add_one (-u)
    by_cases hn : N₃ ≤ n
    · have hA_le : A u 0 ω ≤ A (-((n + 1 : ℕ) : ℝ)) 0 ω := by
        apply flowMeasure_mono_left hA _ hu0
        push_cast; linarith
      have hC_ge : C (-(n : ℝ)) 0 ω ≤ C u 0 ω := by
        apply flowMeasure_mono_left hC (by linarith) (by linarith)
      have hA_bound : A (-((n + 1 : ℕ) : ℝ)) 0 ω ≤ c' * ((n + 1 : ℕ) : ℝ) := by
        have h := hN₁ (n + 1) (by omega) (by omega)
        exact (div_le_iff₀ (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))).mp h
      have hC_bound : d' * (n : ℝ) ≤ C (-(n : ℝ)) 0 ω := by
        have h := hN₂ n (by omega) (by omega)
        exact (le_div_iff₀ (Nat.cast_pos.mpr (by omega) : (0 : ℝ) < (n : ℝ))).mp h
      have hdiff : c' * ((n + 1 : ℕ) : ℝ) - d' * (n : ℝ) ≤ 0 := by
        have h1 : c' < (N₃ : ℝ) * (d' - c') := (div_lt_iff₀ hcd').mp hN₃_c
        have h2 : (d' - c') * (N₃ : ℝ) ≤ (d' - c') * (n : ℝ) :=
          mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hn) hcd'.le
        push_cast
        linarith
      have hA_nn : 0 ≤ A (-(N₃ : ℝ)) 0 ω := hA.1 (-(N₃ : ℝ)) 0 ω (by linarith)
      linarith
    · have hn_lt : n < N₃ := Nat.lt_of_not_le hn
      have hn1_le : (n : ℝ) + 1 ≤ (N₃ : ℝ) := by exact_mod_cast hn_lt
      have hA_le : A u 0 ω ≤ A (-(N₃ : ℝ)) 0 ω :=
        flowMeasure_mono_left hA (by linarith) hu0 ω
      have hC_nn : 0 ≤ C u 0 ω := hC.1 u 0 ω hu0
      linarith
  refine ⟨W, hcompat, ?_, ?_, ?_⟩
  · filter_upwards [hbdd0_ae] with ω h0 t
    exact ⟨bddAbove_fluidLoynesSet_all hA hC h0 t, rfl⟩
  · filter_upwards [hbdd0_ae] with ω h0
    exact isFluidWorkloadPath_of_bddAbove hA hC h0
  · intro W' _ hW'
    filter_upwards [hbdd0_ae, hW'] with ω h0 hW'ω t
    exact minimal_of_isFluidWorkloadPath hA hC h0 hW'ω t

#print axioms solution
