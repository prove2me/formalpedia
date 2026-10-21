-- Prove2me | solution 1 for RobbinsSeqDesign.OptionalStopping.rejects_infinitely_often
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:58:37.596698+00:00
-- url     : https://prove2.me/submissions/4d696c38-aecb-4149-8ec7-62247163754d

import Mathlib
import Definitions.Def_RobbinsSeqDesign_OptionalStopping_Setup

set_option autoImplicit false
open MeasureTheory ProbabilityTheory RobbinsSeqDesign.OptionalStopping Filter Topology
open scoped NNReal ENNReal

lemma rso_S_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (n : ℕ) :
    P.map (S X n) = gaussianReal 0 n := by
  induction n with
  | zero =>
    have h0 : S X 0 = fun _ => (0 : ℝ) := by
      funext ω; simp [S]
    rw [h0, Measure.map_const]
    simp [gaussianReal_zero_var]
  | succ n ih =>
    have hS : S X (n + 1) = S X n + X n := by
      funext ω; simp [S, Finset.sum_range_succ]
    have hS' : S X n = ∑ j ∈ Finset.range n, X j := by
      funext ω; simp [S]
    have hind : IndepFun (S X n) (X n) P := by
      rw [hS']
      exact hindep.indepFun_finsetSum_of_notMem₀ (fun i => (hlaw i).aemeasurable)
        (by simp)
    rw [hS, gaussianReal_add_gaussianReal_of_indepFun hind ih (hlaw n).map_eq]
    have : ((n + 1 : ℕ) : ℝ≥0) = (n : ℝ≥0) + 1 := by push_cast; rfl
    rw [this, add_zero]

lemma rso_tail_measure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    P {ω | c * Real.sqrt n < S X n ω} = gaussianReal 0 1 (Set.Ioi c) := by
  have hSm : AEMeasurable (S X n) P := by
    have : S X n = ∑ j ∈ Finset.range n, X j := by funext ω; simp [S]
    rw [this]
    exact Finset.aemeasurable_sum _ (fun i _ => (hlaw i).aemeasurable)
  have hS : HasLaw (S X n) (gaussianReal 0 n) P := ⟨hSm, rso_S_map P X hindep hlaw n⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hD := gaussianReal_div_const hS (Real.sqrt n)
  have e1 : (0 : ℝ) / Real.sqrt n = 0 := zero_div _
  have e2 : ((n : ℝ≥0) / NNReal.mk (Real.sqrt n ^ 2) (sq_nonneg _)) = 1 := by
    apply NNReal.eq
    simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_mk, NNReal.coe_one]
    rw [Real.sq_sqrt hn0.le]
    exact div_self hn0.ne'
  rw [e1, e2] at hD
  have hset : {ω | c * Real.sqrt n < S X n ω} = {ω | c < S X n ω / Real.sqrt n} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [lt_div_iff₀ hsq]
  rw [hset, hD.measure_eq (p := fun x => c < x) measurableSet_Ioi]
  rfl

lemma rso_q_pos (c : ℝ) : 0 < gaussianReal 0 1 (Set.Ioi c) := by
  rw [pos_iff_ne_zero]
  intro h
  have := (gaussianReal_absolutelyContinuous' 0 (one_ne_zero)) h
  rw [Real.volume_Ioi] at this
  exact ENNReal.top_ne_zero this

lemma rso_limsup_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℕ → Set Ω) (hB : ∀ n, MeasurableSet (B n)) (q : ℝ≥0∞)
    (hq : ∀ n, 1 ≤ n → q ≤ P (B n)) :
    q ≤ P {ω | ∃ᶠ n in atTop, ω ∈ B n} := by
  have e : {ω | ∃ᶠ n in atTop, ω ∈ B n} = ⋂ M : ℕ, ⋃ n, ⋃ (_ : M + 1 ≤ n), B n := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, frequently_atTop]
    constructor
    · intro h M
      obtain ⟨b, hb, hbm⟩ := h (M + 1)
      exact ⟨b, hb, hbm⟩
    · intro h a
      obtain ⟨b, hb, hbm⟩ := h a
      exact ⟨b, by omega, hbm⟩
  rw [e]
  have hmeas : ∀ M : ℕ, MeasurableSet (⋃ n, ⋃ (_ : M + 1 ≤ n), B n) := fun M =>
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => hB n
  have hanti : Antitone (fun M : ℕ => ⋃ n, ⋃ (_ : M + 1 ≤ n), B n) := by
    intro M M' hMM'
    exact Set.iUnion_mono fun n => Set.iUnion_mono' fun hn => ⟨by omega, le_rfl⟩
  have ht := tendsto_measure_iInter_atTop (μ := P)
    (s := fun M : ℕ => ⋃ n, ⋃ (_ : M + 1 ≤ n), B n)
    (fun M => (hmeas M).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  refine ge_of_tendsto ht (Eventually.of_forall fun M => ?_)
  exact (hq (M + 1) (by omega)).trans
    (measure_mono (Set.subset_iUnion₂ (s := fun n (_ : M + 1 ≤ n) => B n) (M + 1) le_rfl))

/-- the event `∃ᶠ n, c √n < S_n - S_N` -/
def rsoA {Ω : Type*} (X : ℕ → Ω → ℝ) (N : ℕ) (c : ℝ) : Set Ω :=
  {ω | ∃ᶠ n : ℕ in atTop, c * Real.sqrt n < S X n ω - S X N ω}

/-- the event `∀ m, ∃ᶠ n, (c - 1/(m+1)) √n < S_n - S_N` -/
def rsoD {Ω : Type*} (X : ℕ → Ω → ℝ) (N : ℕ) (c : ℝ) : Set Ω :=
  {ω | ∀ m : ℕ, ∃ᶠ n : ℕ in atTop, (c - 1 / ((m : ℝ) + 1)) * Real.sqrt n < S X n ω - S X N ω}

lemma rsoA_mono {Ω : Type*} (X : ℕ → Ω → ℝ) (N N' : ℕ) {c' c'' : ℝ} (h : c'' < c') (ω : Ω)
    (hω : ω ∈ rsoA X N c') : ω ∈ rsoA X N' c'' := by
  unfold rsoA at *
  simp only [Set.mem_setOf_eq] at *
  have hev : ∀ᶠ n : ℕ in atTop, |S X N ω - S X N' ω| ≤ (c' - c'') * Real.sqrt n := by
    have h1 : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact (h1.const_mul_atTop (sub_pos.2 h)).eventually_ge_atTop _
  refine (hω.and_eventually hev).mono ?_
  rintro n ⟨h1, h2⟩
  have hK : -|S X N ω - S X N' ω| ≤ S X N ω - S X N' ω := neg_abs_le _
  nlinarith

lemma rsoD_eq {Ω : Type*} (X : ℕ → Ω → ℝ) (N : ℕ) (c : ℝ) : rsoD X 0 c = rsoD X N c := by
  have key : ∀ N N' : ℕ, ∀ ω, ω ∈ rsoD X N c → ω ∈ rsoD X N' c := by
    intro N N' ω hω m
    have h1 := hω (2 * m + 1)
    have hlt : c - 1 / ((m : ℝ) + 1) < c - 1 / (((2 * m + 1 : ℕ) : ℝ) + 1) := by
      have : (1 : ℝ) / (((2 * m + 1 : ℕ) : ℝ) + 1) < 1 / ((m : ℝ) + 1) := by
        apply one_div_lt_one_div_of_lt
        · positivity
        · push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      linarith
    exact rsoA_mono X N N' hlt ω h1
  ext ω
  exact ⟨key 0 N ω, key N 0 ω⟩

lemma rso_meas_D {Ω : Type*} [m : MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (N : ℕ)
    (hX : ∀ i, N ≤ i → Measurable (X i)) (c : ℝ) : MeasurableSet (rsoD X N c) := by
  have hSN : ∀ n, N ≤ n → Measurable (fun ω => S X n ω - S X N ω) := by
    intro n hn
    have : (fun ω => S X n ω - S X N ω) = fun ω => ∑ i ∈ Finset.Ico N n, X i ω := by
      funext ω
      unfold S
      rw [Finset.sum_Ico_eq_sub _ hn]
    rw [this]
    exact Finset.measurable_sum _ (fun i hi => hX i (Finset.mem_Ico.1 hi).1)
  have hfreq : ∀ t : ℕ → ℝ, MeasurableSet
      {ω | ∃ᶠ n : ℕ in atTop, t n * Real.sqrt n < S X n ω - S X N ω} := by
    intro t
    have e : {ω | ∃ᶠ n : ℕ in atTop, t n * Real.sqrt n < S X n ω - S X N ω} =
        ⋂ M : ℕ, ⋃ n, ⋃ (_ : M + N ≤ n), {ω | t n * Real.sqrt n < S X n ω - S X N ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, frequently_atTop]
      constructor
      · intro h M
        obtain ⟨b, hb, hbm⟩ := h (M + N)
        exact ⟨b, hb, hbm⟩
      · intro h a
        obtain ⟨b, hb, hbm⟩ := h a
        exact ⟨b, by omega, hbm⟩
    rw [e]
    refine MeasurableSet.iInter fun M => MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun hn => ?_
    exact measurableSet_lt measurable_const (hSN n (by omega))
  have e : rsoD X N c = ⋂ m : ℕ, {ω | ∃ᶠ n : ℕ in atTop,
      (c - 1 / ((m : ℝ) + 1)) * Real.sqrt n < S X n ω - S X N ω} := by
    ext ω; simp [rsoD]
  rw [e]
  exact MeasurableSet.iInter fun m => hfreq (fun _ => c - 1 / ((m : ℝ) + 1))

lemma rso_main {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (α : ℝ) :
    ∀ᵐ ω ∂P, ∃ᶠ n : ℕ in atTop, α * Real.sqrt n < S X n ω := by
  have hS0 : ∀ ω, S X 0 ω = 0 := fun ω => by simp [S]
  have hs : iIndep (fun n => MeasurableSpace.comap (X n) inferInstance) P :=
    (iIndepFun_iff_iIndep _ _ _).1 hindep
  have hle : ∀ n, MeasurableSpace.comap (X n) inferInstance ≤ m0 := fun n => (hXm n).comap_le
  have htail : ∀ c, MeasurableSet[limsup (fun n => MeasurableSpace.comap (X n) inferInstance) atTop]
      (rsoD X 0 c) := by
    intro c
    rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
    intro N
    rw [rsoD_eq X N c]
    refine @rso_meas_D Ω (⨆ i ≥ N, MeasurableSpace.comap (X i) inferInstance) X N
      (fun i hi => ?_) c
    have : MeasurableSpace.comap (X i) inferInstance ≤
        ⨆ j ≥ N, MeasurableSpace.comap (X j) inferInstance :=
      le_iSup₂ (f := fun j (_ : j ≥ N) => MeasurableSpace.comap (X j) inferInstance) i hi
    exact measurable_iff_comap_le.2 this
  -- positivity
  have hpos : ∀ c, 0 < P (rsoD X 0 c) := by
    intro c
    have hsub : {ω | ∃ᶠ n : ℕ in atTop, ω ∈ {ω' : Ω | (c + 1) * Real.sqrt n < S X n ω'}} ⊆
        rsoD X 0 c := by
      intro ω hω m
      refine hω.mono fun n hn => ?_
      simp only [Set.mem_setOf_eq] at hn
      rw [hS0]
      have hsq := Real.sqrt_nonneg (n : ℝ)
      have hm : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
      nlinarith
    have hge := rso_limsup_ge P (fun n => {ω : Ω | (c + 1) * Real.sqrt n < S X n ω})
      (fun n => measurableSet_lt measurable_const
        (Finset.measurable_sum _ fun i _ => hXm i))
      (gaussianReal 0 1 (Set.Ioi (c + 1)))
      (fun n hn => (rso_tail_measure P X hindep hlaw n hn (c + 1)).ge)
    exact lt_of_lt_of_le (rso_q_pos (c + 1)) (hge.trans (measure_mono hsub))
  have h01 : ∀ c, P (rsoD X 0 c) = 1 := by
    intro c
    rcases measure_zero_or_one_of_measurableSet_limsup_atTop hle hs (htail c) with h | h
    · exact absurd h (hpos c).ne'
    · exact h
  have hD := h01 (α + 1)
  have hmeas : MeasurableSet (rsoD X 0 (α + 1)) := rso_meas_D X 0 (fun i _ => hXm i) _
  have hcompl : P (rsoD X 0 (α + 1))ᶜ = 0 := (prob_compl_eq_zero_iff hmeas).2 hD
  rw [ae_iff]
  refine measure_mono_null ?_ hcompl
  intro ω hω hD'
  apply hω
  have h0 := hD' 0
  refine h0.mono fun n hn => ?_
  rw [hS0] at hn
  norm_num at hn
  linarith

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (α : ℝ) :
    ∀ᵐ ω ∂P, ∃ᶠ n : ℕ in atTop, α * Real.sqrt n < S X n ω := by
  obtain ⟨X', hX'⟩ : ∃ X' : ℕ → Ω → ℝ, ∀ i, X' i = (hlaw i).aemeasurable.mk (X i) :=
    ⟨_, fun _ => rfl⟩
  have hX'm : ∀ i, Measurable (X' i) := fun i => by
    rw [hX']; exact (hlaw i).aemeasurable.measurable_mk
  have hae : ∀ i, X i =ᵐ[P] X' i := fun i => by
    rw [hX']; exact (hlaw i).aemeasurable.ae_eq_mk
  have hind' : iIndepFun X' P := hindep.congr hae
  have hlaw' : ∀ i, HasLaw (X' i) (gaussianReal 0 1) P := fun i =>
    ⟨(hX'm i).aemeasurable, by rw [← (hlaw i).map_eq]; exact Measure.map_congr (hae i).symm⟩
  filter_upwards [rso_main P X' hX'm hind' hlaw' α, ae_all_iff.2 hae] with ω h1 h2
  have : ∀ n, S X n ω = S X' n ω := fun n => by
    unfold S; exact Finset.sum_congr rfl fun i _ => h2 i
  simpa [this] using h1
