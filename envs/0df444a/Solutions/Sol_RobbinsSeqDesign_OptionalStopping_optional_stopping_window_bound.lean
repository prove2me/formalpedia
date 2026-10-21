-- Prove2me | solution 1 for RobbinsSeqDesign.OptionalStopping.optional_stopping_window_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:05:59.963905+00:00
-- url     : https://prove2.me/submissions/fcedbff1-1579-4f3c-8903-04d39bdc0b49

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


lemma rso_h_eq (u v : ℝ) (hu : 0 ≤ u) (huv : u < v) :
    (v - u) / Real.sqrt (v ^ 2 - u ^ 2) = Real.sqrt (v - u) / Real.sqrt (v + u) := by
  have ha : 0 < v - u := by linarith
  have hb : 0 < v + u := by linarith
  have e : v ^ 2 - u ^ 2 = (v - u) * (v + u) := by ring
  rw [e, Real.sqrt_mul ha.le]
  have h1 : 0 < Real.sqrt (v - u) := Real.sqrt_pos.2 ha
  have h2 : 0 < Real.sqrt (v + u) := Real.sqrt_pos.2 hb
  rw [div_eq_div_iff (by positivity) h2.ne']
  have h3 : Real.sqrt (v - u) * Real.sqrt (v - u) = v - u := Real.mul_self_sqrt ha.le
  nlinarith [h3]

lemma rso_h_anti (u u₁ v : ℝ) (hu₁ : 0 ≤ u₁) (h1 : u₁ ≤ u) (huv : u < v) :
    Real.sqrt (v - u) / Real.sqrt (v + u) ≤ Real.sqrt (v - u₁) / Real.sqrt (v + u₁) := by
  have hb : 0 < v + u₁ := by linarith
  apply div_le_div₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by linarith))
    (Real.sqrt_pos.2 hb) (Real.sqrt_le_sqrt (by linarith))

lemma rso_alg1 (n₁ n₂ : ℝ) (h₁ : 0 < n₁) (h₁₂ : n₁ < n₂) :
    (Real.sqrt (n₂ / n₁) - 1) / Real.sqrt (n₂ / n₁ - 1) =
      (Real.sqrt n₂ - Real.sqrt n₁) / Real.sqrt (n₂ - n₁) := by
  have hs : 0 < Real.sqrt n₁ := Real.sqrt_pos.2 h₁
  have e1 : Real.sqrt (n₂ / n₁) = Real.sqrt n₂ / Real.sqrt n₁ := Real.sqrt_div (by linarith) _
  have e2 : n₂ / n₁ - 1 = (n₂ - n₁) / n₁ := by field_simp
  rw [e1, e2, Real.sqrt_div (by linarith) _]
  have h3 : 0 < Real.sqrt (n₂ - n₁) := Real.sqrt_pos.2 (by linarith)
  field_simp

lemma rso_Phi (α : ℝ) : (gaussianReal 0 1).real (Set.Ioi α) = 1 - Phi α := by
  have h1 : (gaussianReal 0 1).real (Set.Iic α) = Phi α := by
    rw [Measure.real, gaussianReal_apply_eq_integral 0 one_ne_zero,
      ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ _))]
    unfold Phi gaussianPDFReal
    rw [← integral_const_mul]
    · simp
  rw [← h1, ← probReal_compl_eq_one_sub measurableSet_Iic, Set.compl_Iic]

lemma rso_gauss_pos {s : Set ℝ} (hs : volume s ≠ 0) : 0 < gaussianReal 0 1 s := by
  rw [pos_iff_ne_zero]
  intro h
  exact hs ((gaussianReal_absolutelyContinuous' 0 one_ne_zero) h)

lemma rso_psi_anti : Antitone (fun c : ℝ => (gaussianReal 0 1).real (Set.Ioi c)) :=
  fun a b hab => measureReal_mono (Set.Ioi_subset_Ioi hab)

lemma rso_psi_pos (c : ℝ) : 0 < (gaussianReal 0 1).real (Set.Ioi c) :=
  ENNReal.toReal_pos (rso_q_pos c).ne' (measure_ne_top _ _)

lemma rso_psi_lt_one (c : ℝ) : (gaussianReal 0 1).real (Set.Ioi c) < 1 := by
  have h : 0 < (gaussianReal 0 1).real (Set.Iic c) := by
    refine ENNReal.toReal_pos (rso_gauss_pos ?_).ne' (measure_ne_top _ _)
    rw [Real.volume_Iic]; simp
  have : (gaussianReal 0 1).real (Set.Ioi c) = 1 - (gaussianReal 0 1).real (Set.Iic c) := by
    rw [← probReal_compl_eq_one_sub measurableSet_Iic, Set.compl_Iic]
  linarith

lemma rso_box_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (N : ℕ) (a b : ℕ → ℝ)
    (hab : ∀ i, a i < b i) :
    0 < P (⋂ i ∈ Finset.range N, X i ⁻¹' Set.Ioo (a i) (b i)) := by
  have hs : iIndep (fun n => MeasurableSpace.comap (X n) inferInstance) P :=
    (iIndepFun_iff_iIndep _ _ _).1 hindep
  rw [hs.meas_biInter (S := Finset.range N) (s := fun i => X i ⁻¹' Set.Ioo (a i) (b i))
    (fun i _ => ⟨_, measurableSet_Ioo, rfl⟩)]
  rw [pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  have : P (X i ⁻¹' Set.Ioo (a i) (b i)) = gaussianReal 0 1 (Set.Ioo (a i) (b i)) := by
    rw [← (hlaw i).map_eq, Measure.map_apply (hXm i) measurableSet_Ioo]
  rw [this]
  refine (rso_gauss_pos ?_).ne'
  rw [Real.volume_Ioo]
  simp [hab i]

/-- first passage event -/
def rsoE {Ω : Type*} (X : ℕ → Ω → ℝ) (α : ℝ) (n₁ n : ℕ) : Set Ω :=
  {ω | (∀ k, n₁ ≤ k → k < n → S X k ω ≤ α * Real.sqrt k) ∧ α * Real.sqrt n < S X n ω}

lemma rso_meas_S {Ω : Type*} [m : MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (n : ℕ)
    (hX : ∀ i, i < n → Measurable (X i)) (k : ℕ) (hk : k ≤ n) : Measurable (S X k) :=
  Finset.measurable_sum _ (fun i hi => hX i (lt_of_lt_of_le (Finset.mem_range.1 hi) hk))

lemma rso_meas_E {Ω : Type*} [m : MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (α : ℝ) (n₁ n : ℕ)
    (hX : ∀ i, i < n → Measurable (X i)) : MeasurableSet (rsoE X α n₁ n) := by
  have e : rsoE X α n₁ n = {ω | α * Real.sqrt n < S X n ω} ∩
      ⋂ k ∈ Finset.Ico n₁ n, {ω | S X k ω ≤ α * Real.sqrt k} := by
    ext ω
    simp only [rsoE, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, fun k hk => h1 k hk.1 hk.2⟩
    · rintro ⟨h2, h1⟩
      exact ⟨fun k hk1 hk2 => h1 k ⟨hk1, hk2⟩, h2⟩
  rw [e]
  refine MeasurableSet.inter ?_ (Finset.measurableSet_biInter _ fun k hk => ?_)
  · exact measurableSet_lt measurable_const (rso_meas_S X n hX n le_rfl)
  · exact measurableSet_le (rso_meas_S X n hX k (Finset.mem_Ico.1 hk).2.le) measurable_const

lemma rso_meas_block {Ω : Type*} [m : MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (n n₂ : ℕ)
    (hn : n ≤ n₂) (hX : ∀ i, n ≤ i → i < n₂ → Measurable (X i)) (a : ℝ) :
    MeasurableSet {ω | a < S X n₂ ω - S X n ω} := by
  have : (fun ω => S X n₂ ω - S X n ω) = fun ω => ∑ i ∈ Finset.Ico n n₂, X i ω := by
    funext ω
    unfold S
    rw [Finset.sum_Ico_eq_sub _ hn]
  have hm : Measurable (fun ω => S X n₂ ω - S X n ω) := by
    rw [this]
    exact Finset.measurable_sum _ (fun i hi => hX i (Finset.mem_Ico.1 hi).1 (Finset.mem_Ico.1 hi).2)
  exact measurableSet_lt measurable_const hm

lemma rso_indep_inter {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hindep : iIndepFun X P) (α : ℝ)
    (n₁ n n₂ : ℕ) (hn : n ≤ n₂) (a : ℝ) :
    P (rsoE X α n₁ n ∩ {ω | a < S X n₂ ω - S X n ω}) =
      P (rsoE X α n₁ n) * P {ω | a < S X n₂ ω - S X n ω} := by
  have hs : iIndep (fun n => MeasurableSpace.comap (X n) inferInstance) P :=
    (iIndepFun_iff_iIndep _ _ _).1 hindep
  have hle : ∀ n, MeasurableSpace.comap (X n) inferInstance ≤ m0 := fun n => (hXm n).comap_le
  have hdisj : Disjoint (Set.Iio n) (Set.Ico n n₂) := by
    rw [Set.disjoint_left]
    intro i hi hi'
    exact absurd hi'.1 (not_le.2 hi)
  have hI := indep_iSup_of_disjoint hle hs hdisj
  rw [Indep_iff] at hI
  apply hI
  · refine @rso_meas_E Ω (⨆ i ∈ Set.Iio n, MeasurableSpace.comap (X i) inferInstance) X α n₁ n
      (fun i hi => ?_)
    have : MeasurableSpace.comap (X i) inferInstance ≤
        ⨆ j ∈ Set.Iio n, MeasurableSpace.comap (X j) inferInstance :=
      le_iSup₂ (f := fun j (_ : j ∈ Set.Iio n) => MeasurableSpace.comap (X j) inferInstance) i hi
    exact measurable_iff_comap_le.2 this
  · refine @rso_meas_block Ω (⨆ i ∈ Set.Ico n n₂, MeasurableSpace.comap (X i) inferInstance) X n n₂
      hn (fun i hi1 hi2 => ?_) a
    have : MeasurableSpace.comap (X i) inferInstance ≤
        ⨆ j ∈ Set.Ico n n₂, MeasurableSpace.comap (X j) inferInstance :=
      le_iSup₂ (f := fun j (_ : j ∈ Set.Ico n n₂) => MeasurableSpace.comap (X j) inferInstance)
        i ⟨hi1, hi2⟩
    exact measurable_iff_comap_le.2 this

lemma rso_block_measure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (n m : ℕ) (hm : 1 ≤ m) (a : ℝ) :
    P {ω | a < S X (n + m) ω - S X n ω} =
      gaussianReal 0 1 (Set.Ioi (a / Real.sqrt m)) := by
  have hind' : iIndepFun (fun i => X (n + i)) P := hindep.precomp (g := fun i => n + i)
    (add_right_injective n)
  have hlaw' : ∀ i, HasLaw (X (n + i)) (gaussianReal 0 1) P := fun i => hlaw (n + i)
  have h := rso_tail_measure P (fun i => X (n + i)) hind' hlaw' m hm (a / Real.sqrt m)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  rw [← h]
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq]
  rw [div_mul_cancel₀ _ hsq.ne']
  have : S (fun i => X (n + i)) m ω = S X (n + m) ω - S X n ω := by
    unfold S
    rw [Finset.sum_range_add]
    ring
  rw [this]

lemma rso_union_iff {Ω : Type*} (X : ℕ → Ω → ℝ) (α : ℝ) (n₁ n₂ : ℕ) (ω : Ω) :
    (∃ n : ℕ, n₁ ≤ n ∧ n ≤ n₂ ∧ α * Real.sqrt n < S X n ω) ↔
      ∃ n ∈ Finset.Icc n₁ n₂, ω ∈ rsoE X α n₁ n := by
  constructor
  · intro h
    have hex : ∃ n : ℕ, n₁ ≤ n ∧ n ≤ n₂ ∧ α * Real.sqrt n < S X n ω := h
    have hspec := Nat.find_spec hex
    refine ⟨Nat.find hex, Finset.mem_Icc.2 ⟨hspec.1, hspec.2.1⟩, ?_, hspec.2.2⟩
    intro k hk1 hk2
    by_contra hcon
    push_neg at hcon
    exact Nat.find_min hex hk2 ⟨hk1, by omega, hcon⟩
  · rintro ⟨n, hn, hω⟩
    exact ⟨n, (Finset.mem_Icc.1 hn).1, (Finset.mem_Icc.1 hn).2, hω.2⟩

lemma rso_disj {Ω : Type*} (X : ℕ → Ω → ℝ) (α : ℝ) (n₁ n₂ : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.Icc n₁ n₂) : Set ℕ) (rsoE X α n₁) := by
  intro n hn m hm hnm
  rw [Function.onFun, Set.disjoint_left]
  intro ω h1 h2
  rcases lt_or_gt_of_ne hnm with h | h
  · have := h2.1 n (Finset.mem_Icc.1 hn).1 h
    exact absurd h1.2 (not_lt.2 this)
  · have := h1.1 m (Finset.mem_Icc.1 hm).1 h
    exact absurd h2.2 (not_lt.2 this)

lemma rso_hfun (n₁ n n₂ : ℕ) (h1 : n₁ ≤ n) (hn : n < n₂) (hn₁ : 1 ≤ n₁) :
    (Real.sqrt n₂ - Real.sqrt n) / Real.sqrt ((n₂ : ℝ) - n) ≤
      (Real.sqrt n₂ - Real.sqrt n₁) / Real.sqrt ((n₂ : ℝ) - n₁) := by
  have hn₁r : (0 : ℝ) < n₁ := by exact_mod_cast hn₁
  have h1r : (n₁ : ℝ) ≤ n := by exact_mod_cast h1
  have hnr : (n : ℝ) < n₂ := by exact_mod_cast hn
  have hu₁ : 0 ≤ Real.sqrt n₁ := Real.sqrt_nonneg _
  have hu : Real.sqrt n₁ ≤ Real.sqrt n := Real.sqrt_le_sqrt h1r
  have huv : Real.sqrt n < Real.sqrt n₂ := Real.sqrt_lt_sqrt (by positivity) hnr
  have e : ∀ k : ℕ, (n₂ : ℝ) - k = Real.sqrt n₂ ^ 2 - Real.sqrt k ^ 2 := fun k => by
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  rw [e n, e n₁, rso_h_eq _ _ (Real.sqrt_nonneg _) huv,
    rso_h_eq _ _ (Real.sqrt_nonneg _) (lt_of_le_of_lt hu huv)]
  exact rso_h_anti _ _ _ hu₁ hu huv

lemma rso_posE {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (α : ℝ) (hα : 0 < α) (n₁ n₂ : ℕ)
    (hn₂ : 1 ≤ n₂) : 0 < P (rsoE X α n₁ n₂) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = α * Real.sqrt n₂ + n₂ := ⟨_, rfl⟩
  have hbox := rso_box_pos P X hXm hindep hlaw n₂ (fun i => if i < n₂ - 1 then -1 else M)
    (fun i => if i < n₂ - 1 then 0 else M + 1) (by
      intro i
      show (if i < n₂ - 1 then (-1 : ℝ) else M) < (if i < n₂ - 1 then (0 : ℝ) else M + 1)
      split_ifs <;> linarith)
  refine lt_of_lt_of_le hbox (measure_mono ?_)
  intro ω hω
  simp only [Set.mem_iInter, Set.mem_preimage, Finset.mem_range] at hω
  have hneg : ∀ i, i < n₂ - 1 → -1 < X i ω ∧ X i ω < 0 := fun i hi => by
    have := hω i (by omega)
    simpa [hi] using this
  have hlast : M < X (n₂ - 1) ω := by
    have h := hω (n₂ - 1) (by omega)
    have h' : ¬ (n₂ - 1 < n₂ - 1) := lt_irrefl _
    simp only [h', if_false] at h
    exact h.1
  refine ⟨fun k hk1 hk2 => ?_, ?_⟩
  · have h1 : S X k ω ≤ 0 := Finset.sum_nonpos (fun i hi =>
      (hneg i (by have := Finset.mem_range.1 hi; omega)).2.le)
    have h2 : 0 ≤ α * Real.sqrt k := by positivity
    linarith
  · have hs : S X n₂ ω = S X (n₂ - 1) ω + X (n₂ - 1) ω := by
      unfold S
      conv_lhs => rw [show n₂ = (n₂ - 1) + 1 by omega]
      rw [Finset.sum_range_succ]
    have hlow : -((n₂ - 1 : ℕ) : ℝ) ≤ S X (n₂ - 1) ω := by
      calc -((n₂ - 1 : ℕ) : ℝ) = ∑ i ∈ Finset.range (n₂ - 1), (-1 : ℝ) := by simp
        _ ≤ S X (n₂ - 1) ω := Finset.sum_le_sum (fun i hi =>
          (hneg i (Finset.mem_range.1 hi)).1.le)
    have hc : ((n₂ - 1 : ℕ) : ℝ) = (n₂ : ℝ) - 1 := Nat.cast_sub hn₂ |>.trans (by simp)
    rw [hs]
    rw [hc] at hlow
    linarith

lemma rso_main_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (n₁ n₂ : ℕ) (hn₁ : 1 ≤ n₁)
    (hn₁₂ : n₁ < n₂) (α : ℝ) (hα : 0 < α) :
    P.real {ω | ∃ n : ℕ, n₁ ≤ n ∧ n ≤ n₂ ∧ α * Real.sqrt n < S X n ω} *
        (gaussianReal 0 1).real
          (Set.Ioi (α * ((Real.sqrt n₂ - Real.sqrt n₁) / Real.sqrt ((n₂ : ℝ) - n₁)))) <
      (gaussianReal 0 1).real (Set.Ioi α) := by
  obtain ⟨ψ1, hψ1⟩ : ∃ ψ1 : ℝ, ψ1 = (gaussianReal 0 1).real
      (Set.Ioi (α * ((Real.sqrt n₂ - Real.sqrt n₁) / Real.sqrt ((n₂ : ℝ) - n₁)))) := ⟨_, rfl⟩
  rw [← hψ1]
  have hψ1lt : ψ1 < 1 := hψ1 ▸ rso_psi_lt_one _
  set F : Set Ω := {ω | α * Real.sqrt n₂ < S X n₂ ω} with hFdef
  have hFmeas : MeasurableSet F :=
    measurableSet_lt measurable_const (rso_meas_S X n₂ (fun i _ => hXm i) n₂ le_rfl)
  have hF : P.real F = (gaussianReal 0 1).real (Set.Ioi α) := by
    rw [Measure.real, Measure.real, hFdef, rso_tail_measure P X hindep hlaw n₂ (by omega) α]
  have hE : {ω | ∃ n : ℕ, n₁ ≤ n ∧ n ≤ n₂ ∧ α * Real.sqrt n < S X n ω} =
      ⋃ n ∈ Finset.Icc n₁ n₂, rsoE X α n₁ n := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    exact rso_union_iff X α n₁ n₂ ω
  have hmeasE : ∀ n ∈ Finset.Icc n₁ n₂, MeasurableSet (rsoE X α n₁ n) :=
    fun n _ => rso_meas_E X α n₁ n (fun i _ => hXm i)
  have hg : P.real {ω | ∃ n : ℕ, n₁ ≤ n ∧ n ≤ n₂ ∧ α * Real.sqrt n < S X n ω} =
      ∑ n ∈ Finset.Icc n₁ n₂, P.real (rsoE X α n₁ n) := by
    rw [hE]
    exact measureReal_biUnion_finset (rso_disj X α n₁ n₂) hmeasE
  have hFsum : ∑ n ∈ Finset.Icc n₁ n₂, P.real (rsoE X α n₁ n ∩ F) ≤ P.real F := by
    have hdisj' : Set.PairwiseDisjoint (↑(Finset.Icc n₁ n₂) : Set ℕ)
        (fun n => rsoE X α n₁ n ∩ F) := fun n hn m hm hnm =>
      Disjoint.mono Set.inter_subset_left Set.inter_subset_left (rso_disj X α n₁ n₂ hn hm hnm)
    rw [← measureReal_biUnion_finset hdisj' (fun n hn => (hmeasE n hn).inter hFmeas)]
    exact measureReal_mono (Set.iUnion₂_subset fun n hn => Set.inter_subset_right)
  have hterm : ∀ n ∈ Finset.Icc n₁ n₂,
      ψ1 * P.real (rsoE X α n₁ n) ≤ P.real (rsoE X α n₁ n ∩ F) := by
    intro n hn
    have hn' := Finset.mem_Icc.1 hn
    rcases eq_or_lt_of_le hn'.2 with hn2 | hn2
    · subst hn2
      have : rsoE X α n₁ n ∩ F = rsoE X α n₁ n := Set.inter_eq_left.2 (fun ω hω => hω.2)
      rw [this]
      exact mul_le_of_le_one_left ENNReal.toReal_nonneg hψ1lt.le
    · -- n < n₂
      have hG := rso_indep_inter P X hXm hindep α n₁ n n₂ hn2.le (α * (Real.sqrt n₂ - Real.sqrt n))
      have hGm := rso_block_measure P X hindep hlaw n (n₂ - n) (by omega)
        (α * (Real.sqrt n₂ - Real.sqrt n))
      rw [Nat.add_sub_cancel' hn2.le] at hGm
      rw [hGm] at hG
      have hsub : rsoE X α n₁ n ∩ {ω | α * (Real.sqrt n₂ - Real.sqrt n) < S X n₂ ω - S X n ω} ⊆
          rsoE X α n₁ n ∩ F := by
        rintro ω ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        simp only [hFdef, Set.mem_setOf_eq] at h2 ⊢
        have := h1.2
        nlinarith
      have hge : P.real (rsoE X α n₁ n ∩ {ω | α * (Real.sqrt n₂ - Real.sqrt n) <
          S X n₂ ω - S X n ω}) ≤ P.real (rsoE X α n₁ n ∩ F) := measureReal_mono hsub
      have hreal : P.real (rsoE X α n₁ n ∩ {ω | α * (Real.sqrt n₂ - Real.sqrt n) <
          S X n₂ ω - S X n ω}) = P.real (rsoE X α n₁ n) *
          (gaussianReal 0 1).real (Set.Ioi (α * (Real.sqrt n₂ - Real.sqrt n) /
            Real.sqrt ((n₂ - n : ℕ) : ℝ))) := by
        rw [Measure.real, hG, ENNReal.toReal_mul]
        rfl
      have hcn : α * (Real.sqrt n₂ - Real.sqrt n) / Real.sqrt ((n₂ - n : ℕ) : ℝ) ≤
          α * ((Real.sqrt n₂ - Real.sqrt n₁) / Real.sqrt ((n₂ : ℝ) - n₁)) := by
        rw [Nat.cast_sub hn2.le, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (rso_hfun n₁ n n₂ hn'.1 hn2 hn₁) hα.le
      have hψ : ψ1 ≤ (gaussianReal 0 1).real (Set.Ioi (α * (Real.sqrt n₂ - Real.sqrt n) /
          Real.sqrt ((n₂ - n : ℕ) : ℝ))) := hψ1 ▸ rso_psi_anti hcn
      calc ψ1 * P.real (rsoE X α n₁ n) = P.real (rsoE X α n₁ n) * ψ1 := mul_comm _ _
        _ ≤ P.real (rsoE X α n₁ n) * (gaussianReal 0 1).real (Set.Ioi (α * (Real.sqrt n₂ -
            Real.sqrt n) / Real.sqrt ((n₂ - n : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hψ ENNReal.toReal_nonneg
        _ = _ := hreal.symm
        _ ≤ _ := hge
  have hstrict : ψ1 * P.real (rsoE X α n₁ n₂) < P.real (rsoE X α n₁ n₂ ∩ F) := by
    have : rsoE X α n₁ n₂ ∩ F = rsoE X α n₁ n₂ := Set.inter_eq_left.2 (fun ω hω => hω.2)
    rw [this]
    have hpos : 0 < P.real (rsoE X α n₁ n₂) :=
      ENNReal.toReal_pos (rso_posE P X hXm hindep hlaw α hα n₁ n₂ (by omega)).ne'
        (measure_ne_top _ _)
    exact mul_lt_of_lt_one_left hpos hψ1lt
  rw [hg, ← hF, Finset.sum_mul]
  calc ∑ n ∈ Finset.Icc n₁ n₂, P.real (rsoE X α n₁ n) * ψ1
      = ∑ n ∈ Finset.Icc n₁ n₂, ψ1 * P.real (rsoE X α n₁ n) :=
        Finset.sum_congr rfl fun n _ => mul_comm _ _
    _ < ∑ n ∈ Finset.Icc n₁ n₂, P.real (rsoE X α n₁ n ∩ F) :=
        Finset.sum_lt_sum hterm ⟨n₂, Finset.mem_Icc.2 ⟨hn₁₂.le, le_rfl⟩, hstrict⟩
    _ ≤ P.real F := hFsum

lemma rso_main_neg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (n₁ n₂ : ℕ) (hn₁ : 1 ≤ n₁)
    (α : ℝ) (hα : α ≤ 0) :
    P.real {ω | ∃ n : ℕ, n₁ ≤ n ∧ n ≤ n₂ ∧ α * Real.sqrt n < S X n ω} < 1 := by
  set E : Set Ω := {ω | ∃ n : ℕ, n₁ ≤ n ∧ n ≤ n₂ ∧ α * Real.sqrt n < S X n ω} with hEdef
  have hE : E = ⋃ n ∈ Finset.Icc n₁ n₂, rsoE X α n₁ n := by
    ext ω
    simp only [hEdef, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    exact rso_union_iff X α n₁ n₂ ω
  have hEm : MeasurableSet E := by
    rw [hE]
    exact Finset.measurableSet_biUnion _ fun n _ => rso_meas_E X α n₁ n (fun i _ => hXm i)
  have hbox := rso_box_pos P X hXm hindep hlaw n₂ (fun _ => α - 1) (fun _ => α) (fun i => by
    show α - 1 < α
    linarith)
  have hsub : (⋂ i ∈ Finset.range n₂, X i ⁻¹' Set.Ioo (α - 1) α) ⊆ Eᶜ := by
    intro ω hω hωE
    simp only [Set.mem_iInter, Set.mem_preimage, Finset.mem_range] at hω
    obtain ⟨n, hn1, hn2, hn3⟩ := hωE
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans hn₁ hn1)
    have h1 : S X n ω ≤ n * α := by
      calc S X n ω ≤ ∑ i ∈ Finset.range n, α := Finset.sum_le_sum (fun i hi =>
            (hω i (by have := Finset.mem_range.1 hi; omega)).2.le)
        _ = n * α := by simp
    have hsq : Real.sqrt n ≤ n := by
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith, by nlinarith⟩
    have h2 : n * α ≤ α * Real.sqrt n := by nlinarith
    linarith
  have hcpos : 0 < P Eᶜ := lt_of_lt_of_le hbox (measure_mono hsub)
  have hcpos' : 0 < P.real Eᶜ := ENNReal.toReal_pos hcpos.ne' (measure_ne_top _ _)
  have := probReal_compl_eq_one_sub (μ := P) hEm
  linarith

lemma rso_final_meas {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (n₁ n₂ : ℕ) (hn₁ : 1 ≤ n₁)
    (hn₁₂ : n₁ < n₂) (α : ℝ) :
    g P X n₁ n₂ α <
      (1 - Phi α) /
        (1 - Phi (α * ((Real.sqrt ((n₂ : ℝ) / n₁) - 1) / Real.sqrt ((n₂ : ℝ) / n₁ - 1)))) := by
  have hn₁r : (0 : ℝ) < n₁ := by exact_mod_cast hn₁
  have hn₁₂r : (n₁ : ℝ) < n₂ := by exact_mod_cast hn₁₂
  rw [rso_alg1 _ _ hn₁r hn₁₂r, ← rso_Phi α]
  set f : ℝ := (Real.sqrt n₂ - Real.sqrt n₁) / Real.sqrt ((n₂ : ℝ) - n₁) with hf
  rw [← rso_Phi (α * f)]
  unfold g
  by_cases hα : 0 < α
  · rw [lt_div_iff₀ (rso_psi_pos _)]
    exact rso_main_pos P X hXm hindep hlaw n₁ n₂ hn₁ hn₁₂ α hα
  · push_neg at hα
    have hlt := rso_main_neg P X hXm hindep hlaw n₁ n₂ hn₁ α hα
    have hu₁ : 0 ≤ Real.sqrt n₁ := Real.sqrt_nonneg _
    have huv : Real.sqrt n₁ < Real.sqrt n₂ := Real.sqrt_lt_sqrt hn₁r.le hn₁₂r
    have hfe : f = Real.sqrt (Real.sqrt n₂ - Real.sqrt n₁) / Real.sqrt (Real.sqrt n₂ + Real.sqrt n₁) := by
      rw [hf, ← rso_h_eq _ _ hu₁ huv, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    have hf1 : f ≤ 1 := by
      rw [hfe]
      have hb : 0 < Real.sqrt (Real.sqrt n₂ + Real.sqrt n₁) := Real.sqrt_pos.2 (by linarith)
      rw [div_le_one hb]
      exact Real.sqrt_le_sqrt (by linarith)
    have hf0 : 0 ≤ f := by rw [hfe]; positivity
    have hle : α ≤ α * f := by nlinarith
    calc _ < 1 := hlt
      _ ≤ _ := by
        rw [le_div_iff₀ (rso_psi_pos _), one_mul]
        exact rso_psi_anti hle

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (n₁ n₂ : ℕ) (hn₁ : 1 ≤ n₁)
    (hn₁₂ : n₁ < n₂) (α : ℝ) :
    g P X n₁ n₂ α <
      (1 - Phi α) /
        (1 - Phi (α * ((Real.sqrt ((n₂ : ℝ) / n₁) - 1) / Real.sqrt ((n₂ : ℝ) / n₁ - 1)))) := by
  obtain ⟨X', hX'⟩ : ∃ X' : ℕ → Ω → ℝ, ∀ i, X' i = (hlaw i).aemeasurable.mk (X i) :=
    ⟨_, fun _ => rfl⟩
  have hX'm : ∀ i, Measurable (X' i) := fun i => by
    rw [hX']; exact (hlaw i).aemeasurable.measurable_mk
  have hae : ∀ i, X i =ᵐ[P] X' i := fun i => by
    rw [hX']; exact (hlaw i).aemeasurable.ae_eq_mk
  have hind' : iIndepFun X' P := hindep.congr hae
  have hlaw' : ∀ i, HasLaw (X' i) (gaussianReal 0 1) P := fun i =>
    ⟨(hX'm i).aemeasurable, by rw [← (hlaw i).map_eq]; exact Measure.map_congr (hae i).symm⟩
  have hg : g P X n₁ n₂ α = g P X' n₁ n₂ α := by
    unfold g
    apply measureReal_congr
    rw [Filter.eventuallyEq_set]
    filter_upwards [ae_all_iff.2 hae] with ω hω
    have : ∀ n, S X n ω = S X' n ω := fun n => by
      unfold S; exact Finset.sum_congr rfl fun i _ => hω i
    simp only [Set.mem_setOf_eq, this]
  rw [hg]
  exact rso_final_meas P X' hX'm hind' hlaw' n₁ n₂ hn₁ hn₁₂ α
