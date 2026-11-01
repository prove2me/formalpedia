-- Prove2me | solution 1 for SyncQueues.WaitingTime.eq_6_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:06:21.545334+00:00
-- url     : https://prove2.me/submissions/d292a5d3-55da-4a47-aec7-984838686ce2

import Mathlib
import Definitions.Def_SyncQueues_WaitingTime_BranchingTree
import Definitions.Def_SyncQueues_WaitingTime_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open SyncQueues.WaitingTime

namespace SQE61

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma frequently_of_indep {β : Type*} [MeasurableSpace β] {X : ℕ → Ω → β}
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X P) {A : Set β} (hA : MeasurableSet A)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hlaw : ∀ k, P (X k ⁻¹' A) = c) :
    ∀ᵐ ω ∂P, ∃ᶠ k in atTop, X k ω ∈ A := by
  set s : ℕ → Set Ω := fun k => X k ⁻¹' A
  have hsm : ∀ k, MeasurableSet (s k) := fun k => hX k hA
  have hs : iIndepSet s P := by
    rw [iIndepSet_iff_meas_biInter hsm]
    intro S
    exact hind.measure_inter_preimage_eq_mul S (sets := fun _ => A) (fun _ _ => hA)
  have hsum : (∑' k, P (s k)) = ∞ := by
    simp only [s, hlaw]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hc
  have h1 := measure_limsup_eq_one hsm hs hsum
  have hmeas : MeasurableSet (limsup s atTop) := by
    rw [limsup_eq_iInf_iSup_of_nat]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun i => MeasurableSet.iUnion
      fun _ => hsm i
  have h2 : ∀ᵐ ω ∂P, ω ∈ limsup s atTop := by
    rw [ae_iff]
    have := prob_compl_eq_zero_iff hmeas (μ := P)
    rw [← this.2 h1]
    rfl
  filter_upwards [h2] with ω hω
  exact Filter.mem_limsup_iff_frequently_mem.1 hω


lemma expM_Iic_zero {r : ℝ} (hr : 0 < r) : expMeasure r (Set.Iic 0) = 0 := by
  haveI := isProbabilityMeasure_expMeasure hr
  have h := cdf_expMeasure_eq hr 0
  rw [cdf_eq_real] at h
  simp only [le_refl, if_true, mul_zero, neg_zero, Real.exp_zero, sub_self] at h
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at h
  rcases h with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

lemma expM_Ioi_one {r : ℝ} (hr : 0 < r) : expMeasure r (Set.Ioi 1) ≠ 0 := by
  haveI := isProbabilityMeasure_expMeasure hr
  have h := cdf_expMeasure_eq hr 1
  rw [cdf_eq_real] at h
  simp only [zero_le_one, if_true, mul_one] at h
  intro h0
  have hc : expMeasure r (Set.Iic 1)ᶜ = 0 := by rw [Set.compl_Iic]; exact h0
  rw [prob_compl_eq_one_sub measurableSet_Iic, tsub_eq_zero_iff_le] at hc
  have h1 : expMeasure r (Set.Iic 1) = 1 := le_antisymm prob_le_one hc
  rw [measureReal_def, h1, ENNReal.toReal_one] at h
  have : 0 < Real.exp (-r) := Real.exp_pos _
  linarith

/-- the support of `uniformInj m n` -/
def injSet (m n : ℕ) : Set (Fin m → ℕ) := {ρ | Function.Injective ρ ∧ ∀ i, ρ i < n}

lemma injSet_finite (m n : ℕ) : (injSet m n).Finite := by
  refine Set.Finite.subset (Set.Finite.pi (t := fun _ : Fin m => Set.Iio n)
    (fun _ => Set.finite_Iio n)) ?_
  intro ρ hρ
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iio, forall_const]
  exact hρ.2

lemma swap_mem {m n : ℕ} (hm : 0 < m) (hn : m ≤ n) {s0 : ℕ} (hs0 : s0 < n) :
    (fun i : Fin m => Equiv.swap 0 s0 i.val) ∈ injSet m n ∩ {ρ | s0 ∈ Set.range ρ} := by
  refine ⟨⟨fun i j h => Fin.ext ((Equiv.swap 0 s0).injective h), fun i => ?_⟩,
    ⟨⟨0, hm⟩, by simp⟩⟩
  show Equiv.swap 0 s0 i.val < n
  rcases eq_or_ne i.val 0 with h0 | h0
  · simp [h0, hs0]
  · rcases eq_or_ne i.val s0 with h1 | h1
    · rw [h1, Equiv.swap_apply_right]; omega
    · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]; omega

lemma uniformInj_eq {m n : ℕ} : uniformInj m n = uniformOn (injSet m n) := rfl

lemma uniformInj_prob {m n : ℕ} (hm : 0 < m) (hn : m ≤ n) : IsProbabilityMeasure (uniformInj m n) := by
  constructor
  rw [uniformInj_eq]
  exact uniformOn_of_univ (injSet_finite m n) ⟨_, (swap_mem hm hn (lt_of_lt_of_le hm hn)).1⟩

variable {m n : ℕ} {lam : ℝ} {Bm : Measure (Fin m → ℝ)} [IsProbabilityMeasure Bm]
  {E : ℕ → Ω → ℝ} {R : ℕ → Ω → (Fin m → ℕ)} {C : ℕ → Ω → (Fin m → ℝ)}

lemma prob_triple (hsys : IsSyncSystem P m n lam Bm E R C) (k : ℕ)
    {A : Set ℝ} {B : Set (Fin m → ℕ)} {D : Set (Fin m → ℝ)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hD : MeasurableSet D) :
    P ((fun ω => (E k ω, R k ω, C k ω)) ⁻¹' (A ×ˢ (B ×ˢ D))) =
      expMeasure (lam * n) A * (uniformInj m n B * Bm D) := by
  have hT : Measurable (fun ω => (E k ω, R k ω, C k ω)) :=
    (hsys.1 k).1.prodMk ((hsys.1 k).2.1.prodMk (hsys.1 k).2.2)
  rw [← Measure.map_apply hT (hA.prod (hB.prod hD)), hsys.2.2 k, Measure.prod_prod,
    Measure.prod_prod]

lemma ae_good (hm : 0 < m) (hn : m ≤ n) (hlam : 0 < lam)
    (hsys : IsSyncSystem P m n lam Bm E R C) :
    ∀ᵐ ω ∂P, (∀ k, 0 < E k ω) ∧ (∃ᶠ k in atTop, 1 < E k ω) ∧ (∀ k, R k ω ∈ injSet m n) ∧
      (∀ s0 : ℕ, s0 < n → ∃ᶠ k in atTop, s0 ∈ Set.range (R k ω)) := by
  have hr : 0 < lam * n := mul_pos hlam (by exact_mod_cast lt_of_lt_of_le hm hn)
  haveI := isProbabilityMeasure_expMeasure hr
  haveI := uniformInj_prob hm hn
  set T : ℕ → Ω → ℝ × (Fin m → ℕ) × (Fin m → ℝ) := fun k ω => (E k ω, R k ω, C k ω)
  have hT : ∀ k, Measurable (T k) := fun k =>
    (hsys.1 k).1.prodMk ((hsys.1 k).2.1.prodMk (hsys.1 k).2.2)
  have hdisc : ∀ B : Set (Fin m → ℕ), MeasurableSet B := fun B => B.to_countable.measurableSet
  refine (ae_all_iff.2 fun k => ?_).and ((?_ : ∀ᵐ ω ∂P, ∃ᶠ k in atTop, 1 < E k ω).and
    ((ae_all_iff.2 fun k => ?_).and ?_))
  · -- positivity of the gaps
    have h0 : P ((fun ω => (E k ω, R k ω, C k ω)) ⁻¹' (Set.Iic 0 ×ˢ (Set.univ ×ˢ Set.univ))) = 0 := by
      rw [prob_triple hsys k measurableSet_Iic MeasurableSet.univ MeasurableSet.univ,
        expM_Iic_zero hr, zero_mul]
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) h0
    simp only [Set.mem_setOf_eq, not_lt] at hω
    simp [hω]
  · refine frequently_of_indep (X := T) hT hsys.2.1 (A := Set.Ioi 1 ×ˢ (Set.univ ×ˢ Set.univ))
      (measurableSet_Ioi.prod (MeasurableSet.univ.prod MeasurableSet.univ))
      (c := expMeasure (lam * n) (Set.Ioi 1)) (expM_Ioi_one hr) (fun k => ?_) |>.mono ?_
    · rw [prob_triple hsys k measurableSet_Ioi MeasurableSet.univ MeasurableSet.univ]
      simp
    · intro ω hω
      exact hω.mono fun k hk => by simpa [T] using hk
  · -- routing in the support
    have h0 : P ((fun ω => (E k ω, R k ω, C k ω)) ⁻¹'
        (Set.univ ×ˢ ((injSet m n)ᶜ ×ˢ Set.univ))) = 0 := by
      rw [prob_triple hsys k MeasurableSet.univ (hdisc _) MeasurableSet.univ, uniformInj_eq,
        (uniformOn_eq_zero_iff (injSet_finite m n)).2 (Set.inter_compl_self _)]
      simp
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) h0
    simpa using hω
  · -- every server is used infinitely often
    have hcount : ∀ s0 : ℕ, s0 < n → ∀ᵐ ω ∂P, ∃ᶠ k in atTop, s0 ∈ Set.range (R k ω) := by
      intro s0 hs0
      have hne : uniformInj m n {ρ | s0 ∈ Set.range ρ} ≠ 0 := by
        rw [uniformInj_eq, Ne, uniformOn_eq_zero_iff (injSet_finite m n)]
        exact Set.nonempty_iff_ne_empty.1 ⟨_, swap_mem hm hn hs0⟩
      refine frequently_of_indep (X := T) hT hsys.2.1
        (A := Set.univ ×ˢ ({ρ | s0 ∈ Set.range ρ} ×ˢ Set.univ))
        (MeasurableSet.univ.prod ((hdisc _).prod MeasurableSet.univ))
        (c := uniformInj m n {ρ | s0 ∈ Set.range ρ}) hne (fun k => ?_) |>.mono ?_
      · rw [prob_triple hsys k MeasurableSet.univ (hdisc _) MeasurableSet.univ]
        simp
      · intro ω hω
        exact hω.mono fun k hk => by simpa [T] using hk
    refine ae_all_iff.2 fun s0 => ?_
    by_cases h : s0 < n
    · filter_upwards [hcount s0 h] with ω hω _ using hω
    · exact ae_of_all _ fun ω h' => absurd h' h

end Prob


section Det

variable {m : ℕ} (E : ℕ → ℝ) (R : ℕ → Fin m → ℕ) (C : ℕ → Fin m → ℝ)

lemma arrival_succ_lt (hE : ∀ k, 0 < E k) (k : ℕ) : arrival E (k + 1) < arrival E k := by
  unfold arrival
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp; linarith [hE 0, hE 1]
  · rw [if_neg (by omega), if_neg (by omega), Finset.sum_Icc_succ_top (by omega)]
    linarith [hE (k + 1)]

lemma arrival_strictAnti (hE : ∀ k, 0 < E k) : StrictAnti (arrival E) :=
  strictAnti_nat_of_succ_lt (arrival_succ_lt E hE)

lemma pastCount_spec (hE : ∀ k, 0 < E k) (hdiv : ∀ M : ℝ, ∃ k, arrival E k < M) (t0 : ℝ)
    (k : ℕ) (hk : 1 ≤ k) : k ≤ pastCount E t0 ↔ t0 < arrival E k := by
  have hex : ∃ k, arrival E (k + 1) ≤ t0 := by
    obtain ⟨k, hk⟩ := hdiv t0
    rcases k with _ | k
    · exact ⟨0, (arrival_succ_lt E hE 0).le.trans hk.le⟩
    · exact ⟨k, hk.le⟩
  classical
  set N := Nat.find hex with hN
  have hmem : ∀ k, (1 ≤ k ∧ t0 < arrival E k) ↔ (1 ≤ k ∧ k ≤ N) := by
    intro k
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_contra h3
      push_neg at h3
      have : arrival E k ≤ arrival E (N + 1) := (arrival_strictAnti E hE).antitone (by omega)
      have h4 := Nat.find_spec hex
      rw [← hN] at h4
      linarith
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := Nat.find_min hex (show k - 1 < N by omega)
      rw [show k - 1 + 1 = k by omega] at this
      push_neg at this
      exact this
  have hcard : pastCount E t0 = N := by
    unfold pastCount
    rw [Nat.card_congr (Equiv.subtypeEquivRight hmem)]
    have : Nat.card {k : ℕ // 1 ≤ k ∧ k ≤ N} = Nat.card (Set.Icc 1 N) := rfl
    rw [this, Nat.card_eq_card_toFinset (Set.Icc 1 N), Set.toFinset_Icc, Nat.card_Icc]
    omega
  rw [hcard]
  have := hmem k
  constructor
  · intro h; exact (this.2 ⟨hk, h⟩).2
  · intro h; exact (this.1 ⟨hk, h⟩).2

/-- one step of the fold defining `freeTimes` -/
noncomputable def fstep (t0 : ℝ) (F : ℕ → ℝ) (j : ℕ) : ℕ → ℝ :=
  if t0 < arrival E (j + 1) then admit F (arrival E (j + 1)) (R (j + 1)) (C (j + 1)) else F

/-- the server-free times seen by job `k` (after admitting jobs `K, …, k+1`) -/
noncomputable def Phi (t0 : ℝ) (K k : ℕ) : ℕ → ℝ :=
  ((List.range' k (K - k)).reverse).foldl (fstep E R C t0) (fun _ => t0)

lemma Phi_zero (t0 : ℝ) (K : ℕ) : Phi E R C t0 K 0 = freeTimes E R C t0 K := by
  unfold Phi freeTimes
  rw [List.range_eq_range', Nat.sub_zero]
  rfl

lemma Phi_self (t0 : ℝ) (K : ℕ) : Phi E R C t0 K K = fun _ => t0 := by
  unfold Phi; simp

lemma Phi_step (t0 : ℝ) {K k : ℕ} (hk : k < K) :
    Phi E R C t0 K k = fstep E R C t0 (Phi E R C t0 K (k + 1)) k := by
  unfold Phi
  have : K - k = (K - (k + 1)) + 1 := by omega
  rw [this, List.range'_succ, List.reverse_cons, List.foldl_append]
  rfl

/-- start time of job `k` -/
noncomputable def st (t0 : ℝ) (K k : ℕ) : ℝ := startTime (Phi E R C t0 K k) (arrival E k) (R k)

lemma Phi_spec (t0 : ℝ) (K : ℕ) (hK : ∀ j, 1 ≤ j → j ≤ K → t0 < arrival E j) :
    ∀ d k, k + d = K →
      (∀ s, (∀ k', k < k' → k' ≤ K → s ∉ Set.range (R k')) → Phi E R C t0 K k s = t0) ∧
      (∀ s k', k < k' → k' ≤ K → ∀ h : ∃ i, R k' i = s,
        (∀ k'', k < k'' → k'' < k' → s ∉ Set.range (R k'')) →
        Phi E R C t0 K k s = st E R C t0 K k' + C k' h.choose) := by
  intro d
  induction d with
  | zero =>
    intro k hk
    simp only [add_zero] at hk
    subst hk
    refine ⟨fun s _ => by rw [Phi_self], fun s k' h1 h2 => by omega⟩
  | succ d ih =>
    intro k hk
    obtain ⟨IP, IQ⟩ := ih (k + 1) (by omega)
    have hstep : Phi E R C t0 K k = admit (Phi E R C t0 K (k + 1)) (arrival E (k + 1)) (R (k + 1))
        (C (k + 1)) := by
      rw [Phi_step E R C t0 (show k < K by omega)]
      unfold fstep
      rw [if_pos (hK (k + 1) (by omega) (by omega))]
    constructor
    · intro s hs
      rw [hstep]
      unfold admit
      rw [dif_neg]
      · exact IP s fun k' h1 h2 => hs k' (by omega) h2
      · rintro ⟨i, hi⟩
        exact hs (k + 1) (by omega) (by omega) ⟨i, hi⟩
    · intro s k' h1 h2 h hmin
      rw [hstep]
      unfold admit
      rcases eq_or_lt_of_le (show k + 1 ≤ k' by omega) with h3 | h3
      · subst h3
        rw [dif_pos h]
        rfl
      · rw [dif_neg]
        · exact IQ s k' h3 h2 h fun k'' h4 h5 => hmin k'' (by omega) h5
        · rintro ⟨i, hi⟩
          exact hmin (k + 1) (by omega) h3 ⟨i, hi⟩

variable {E R C}

lemma predJob_spec (hpred : ∀ k i, ∃ k', k < k' ∧ R k i ∈ Set.range (R k')) (k : ℕ) (i : Fin m) :
    k < predJob R k i ∧ R k i ∈ Set.range (R (predJob R k i)) ∧
      ∀ k'', k < k'' → k'' < predJob R k i → R k i ∉ Set.range (R k'') := by
  have hne : ({k' : ℕ | k < k' ∧ R k i ∈ Set.range (R k')}).Nonempty := hpred k i
  have hmem := Nat.sInf_mem hne
  refine ⟨hmem.1, hmem.2, fun k'' h1 h2 h3 => ?_⟩
  exact Nat.notMem_of_lt_sInf h2 ⟨h1, h3⟩

lemma Phi_pred (hpred : ∀ k i, ∃ k', k < k' ∧ R k i ∈ Set.range (R k')) (t0 : ℝ) (K : ℕ)
    (hK : ∀ j, 1 ≤ j → j ≤ K → t0 < arrival E j) {k : ℕ} (hk : k ≤ K) (i : Fin m) :
    (predJob R k i ≤ K → Phi E R C t0 K k (R k i) =
      st E R C t0 K (predJob R k i) + C (predJob R k i) (predPiece R k i)) ∧
    (K < predJob R k i → Phi E R C t0 K k (R k i) = t0) := by
  obtain ⟨IP, IQ⟩ := Phi_spec E R C t0 K hK (K - k) k (by omega)
  obtain ⟨h1, h2, h3⟩ := predJob_spec hpred k i
  constructor
  · intro hp
    have h : ∃ i', R (predJob R k i) i' = R k i := h2
    rw [IQ (R k i) (predJob R k i) h1 hp h h3]
    unfold predPiece
    rw [dif_pos h]
  · intro hp
    apply IP
    intro k' hk1 hk2 hk3
    have := Nat.sInf_le (show k' ∈ {k' : ℕ | k < k' ∧ R k i ∈ Set.range (R k')} from ⟨hk1, hk3⟩)
    have : predJob R k i ≤ k' := this
    omega

/-- waiting time of job `k` in the simulation -/
noncomputable def ws (t0 : ℝ) (K k : ℕ) : ℝ := st E R C t0 K k - arrival E k

lemma ws_nonneg (t0 : ℝ) (K k : ℕ) : 0 ≤ ws (E := E) (R := R) (C := C) t0 K k := by
  unfold ws st startTime
  linarith [le_max_left (arrival E k) (⨆ i, Phi E R C t0 K k (R k i))]

lemma ws_ge (hpred : ∀ k i, ∃ k', k < k' ∧ R k i ∈ Set.range (R k')) (t0 : ℝ) (K : ℕ)
    (hK : ∀ j, 1 ≤ j → j ≤ K → t0 < arrival E j) {k : ℕ} (hk : k ≤ K) (i : Fin m)
    (hp : predJob R k i ≤ K) :
    ws (E := E) (R := R) (C := C) t0 K (predJob R k i) + edgeHat E R C k i ≤
      ws (E := E) (R := R) (C := C) t0 K k := by
  have h := (Phi_pred (C := C) hpred t0 K hK hk i).1 hp
  unfold ws edgeHat
  have hle : Phi E R C t0 K k (R k i) ≤ st E R C t0 K k := by
    unfold st startTime
    exact (le_ciSup (f := fun i => Phi E R C t0 K k (R k i)) (Set.finite_range _).bddAbove
      i).trans (le_max_right _ _)
  rw [h] at hle
  linarith

lemma ws_attained (hm : 0 < m) (hpred : ∀ k i, ∃ k', k < k' ∧ R k i ∈ Set.range (R k'))
    (t0 : ℝ) (K : ℕ) (hK : ∀ j, 1 ≤ j → j ≤ K → t0 < arrival E j) (ht0 : t0 < arrival E 0)
    {k : ℕ} (hk : k ≤ K) :
    ws (E := E) (R := R) (C := C) t0 K k = 0 ∨ ∃ i, predJob R k i ≤ K ∧
      ws (E := E) (R := R) (C := C) t0 K k =
        ws (E := E) (R := R) (C := C) t0 K (predJob R k i) + edgeHat E R C k i := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨i0, hi0⟩ := exists_eq_ciSup_of_finite (f := fun i => Phi E R C t0 K k (R k i))
  have htk : t0 < arrival E k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; exact ht0
    · exact hK k h hk
  rcases le_or_gt (⨆ i, Phi E R C t0 K k (R k i)) (arrival E k) with h | h
  · left
    unfold ws st startTime
    rw [max_eq_left h, sub_self]
  · right
    rw [← hi0] at h
    by_cases hp : predJob R k i0 ≤ K
    · refine ⟨i0, hp, ?_⟩
      have e := (Phi_pred (C := C) hpred t0 K hK hk i0).1 hp
      have hst : st E R C t0 K k = Phi E R C t0 K k (R k i0) := by
        unfold st startTime
        rw [← hi0, max_eq_right h.le]
      unfold ws edgeHat
      rw [hst, e]
      ring
    · have e := (Phi_pred (C := C) hpred t0 K hK hk i0).2 (by omega)
      rw [e] at h
      linarith

/-- path sums from job `k` -/
noncomputable def pf (E : ℕ → ℝ) (R : ℕ → Fin m → ℕ) (C : ℕ → Fin m → ℝ) : ℕ → List (Fin m) → ℝ
  | _, [] => 0
  | k, i :: j => edgeHat E R C k i + pf E R C (predJob R k i) j

/-- the path from job `k` with label `j` stays among the jobs `≤ K` -/
def okP (R : ℕ → Fin m → ℕ) (K : ℕ) : ℕ → List (Fin m) → Prop
  | _, [] => True
  | k, i :: j => predJob R k i ≤ K ∧ okP R K (predJob R k i) j

lemma foldl_pf (j : List (Fin m)) : ∀ (k : ℕ) (c : ℝ),
    (j.foldl (fun (st : ℕ × ℝ) i => (predJob R st.1 i, st.2 + edgeHat E R C st.1 i)) (k, c)).2 =
      c + pf E R C k j := by
  induction j with
  | nil => intro k c; simp [pf]
  | cons i j ih =>
    intro k c
    simp only [List.foldl_cons]
    rw [ih]
    simp only [pf]
    ring

lemma pathSumHat_eq (j : List (Fin m)) : pathSumHat E R C j = pf E R C 0 j := by
  unfold pathSumHat
  rw [foldl_pf, zero_add]

lemma okP_mono {K K' : ℕ} (hKK : K ≤ K') : ∀ (j : List (Fin m)) (k : ℕ), okP R K k j → okP R K' k j
  | [], _, _ => trivial
  | i :: j, k, ⟨h1, h2⟩ => ⟨h1.trans hKK, okP_mono hKK j _ h2⟩

lemma okP_eventually : ∀ (j : List (Fin m)) (k : ℕ), ∃ K0, ∀ K, K0 ≤ K → okP R K k j
  | [], _ => ⟨0, fun _ _ => trivial⟩
  | i :: j, k => by
    obtain ⟨K1, hK1⟩ := okP_eventually j (predJob R k i)
    exact ⟨max (predJob R k i) K1, fun K hK => ⟨le_of_max_le_left hK, hK1 K (le_of_max_le_right hK)⟩⟩

lemma pf_le_ws (hpred : ∀ k i, ∃ k', k < k' ∧ R k i ∈ Set.range (R k')) (t0 : ℝ) (K : ℕ)
    (hK : ∀ j, 1 ≤ j → j ≤ K → t0 < arrival E j) :
    ∀ (j : List (Fin m)) (k : ℕ), k ≤ K → okP R K k j →
      pf E R C k j ≤ ws (E := E) (R := R) (C := C) t0 K k
  | [], k, _, _ => by simp only [pf]; exact ws_nonneg t0 K k
  | i :: j, k, hk, ⟨h1, h2⟩ => by
    simp only [pf]
    have := pf_le_ws hpred t0 K hK j (predJob R k i) h1 h2
    have := ws_ge (C := C) hpred t0 K hK hk i h1
    linarith

lemma ws_eq_pf (hm : 0 < m) (hpred : ∀ k i, ∃ k', k < k' ∧ R k i ∈ Set.range (R k')) (t0 : ℝ)
    (K : ℕ) (hK : ∀ j, 1 ≤ j → j ≤ K → t0 < arrival E j) (ht0 : t0 < arrival E 0) :
    ∀ d k, K - k = d → k ≤ K → ∃ j, okP R K k j ∧ ws (E := E) (R := R) (C := C) t0 K k = pf E R C k j := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro k hd hk
    rcases ws_attained (C := C) hm hpred t0 K hK ht0 hk with h | ⟨i, hp, h⟩
    · exact ⟨[], trivial, by rw [h]; rfl⟩
    · have hlt := (predJob_spec hpred k i).1
      obtain ⟨j, hj1, hj2⟩ := ih (K - predJob R k i) (by omega) (predJob R k i) rfl hp
      refine ⟨i :: j, ⟨hp, hj1⟩, ?_⟩
      rw [h, hj2]
      simp only [pf]
      ring

lemma waitT_eq (t0 : ℝ) :
    waitT E R C t0 = ws (E := E) (R := R) (C := C) t0 (pastCount E t0) 0 := by
  unfold waitT ws st
  rw [Phi_zero]


lemma det_main (hm : 0 < m) (hE : ∀ k, 0 < E k) (hdiv : ∀ M : ℝ, ∃ k, arrival E k < M)
    (hpred : ∀ k i, ∃ k', k < k' ∧ R k i ∈ Set.range (R k')) :
    AntitoneOn (fun t0 => waitT E R C t0) (Set.Iio 0) ∧
      Tendsto (fun t0 => ((waitT E R C t0 : ℝ) : EReal)) atBot
        (𝓝 (⨆ r : ℕ, ((Uhat E R C r : ℝ) : EReal))) := by
  have hK : ∀ t0 : ℝ, ∀ j, 1 ≤ j → j ≤ pastCount E t0 → t0 < arrival E j :=
    fun t0 j hj h => (pastCount_spec E hE hdiv t0 j hj).1 h
  have ha0 : ∀ t0 : ℝ, t0 < 0 → t0 < arrival E 0 := by
    intro t0 ht
    have : arrival E 0 = E 0 := by simp [arrival]
    rw [this]; linarith [hE 0]
  have hrep : ∀ t0 : ℝ, t0 < 0 → ∃ j, okP R (pastCount E t0) 0 j ∧ waitT E R C t0 = pf E R C 0 j := by
    intro t0 ht
    rw [waitT_eq]
    exact ws_eq_pf hm hpred t0 _ (hK t0) (ha0 t0 ht) _ 0 rfl (Nat.zero_le _)
  have hlow : ∀ t0 : ℝ, ∀ j, okP R (pastCount E t0) 0 j → pf E R C 0 j ≤ waitT E R C t0 := by
    intro t0 j hj
    rw [waitT_eq]
    exact pf_le_ws hpred t0 _ (hK t0) j 0 (Nat.zero_le _) hj
  have hNmono : ∀ t1 t2 : ℝ, t1 ≤ t2 → pastCount E t2 ≤ pastCount E t1 := by
    intro t1 t2 h
    rcases Nat.eq_zero_or_pos (pastCount E t2) with h0 | h0
    · rw [h0]; exact Nat.zero_le _
    · exact (pastCount_spec E hE hdiv t1 _ h0).2
        (lt_of_le_of_lt h ((pastCount_spec E hE hdiv t2 _ h0).1 le_rfl))
  have hUhat : ∀ j : List (Fin m), pathSumHat E R C j ≤ Uhat E R C j.length := by
    intro j
    unfold Uhat
    have := le_ciSup (f := fun v : Fin j.length → Fin m => pathSumHat E R C (List.ofFn v))
      (Set.finite_range _).bddAbove j.get
    simpa only [List.ofFn_get] using this
  constructor
  · intro t1 ht1 t2 ht2 h12
    obtain ⟨j, hj, hw⟩ := hrep t2 ht2
    simp only
    rw [hw]
    exact hlow t1 j (okP_mono (hNmono t1 t2 h12) j 0 hj)
  · refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · obtain ⟨r, hr⟩ := lt_iSup_iff.1 hb
      haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      obtain ⟨v, hv⟩ := exists_eq_ciSup_of_finite
        (f := fun v : Fin r → Fin m => pathSumHat E R C (List.ofFn v))
      obtain ⟨K0, hK0⟩ := okP_eventually (R := R) (List.ofFn v) 0
      have hev : ∀ᶠ t0 in atBot, t0 < min (arrival E K0) 0 := eventually_lt_atBot _
      filter_upwards [hev] with t0 ht0
      have hN : K0 ≤ pastCount E t0 := by
        rcases Nat.eq_zero_or_pos K0 with h0 | h0
        · rw [h0]; exact Nat.zero_le _
        · exact (pastCount_spec E hE hdiv t0 K0 h0).2 (lt_of_lt_of_le ht0 (min_le_left _ _))
      have h1 := hlow t0 _ (hK0 _ hN)
      rw [← pathSumHat_eq] at h1
      have h2 : Uhat E R C r = pathSumHat E R C (List.ofFn v) := by unfold Uhat; rw [← hv]
      rw [h2] at hr
      exact lt_of_lt_of_le hr (EReal.coe_le_coe_iff.2 h1)
    · have hev : ∀ᶠ t0 in atBot, t0 < (0 : ℝ) := eventually_lt_atBot _
      filter_upwards [hev] with t0 ht0
      obtain ⟨j, -, hw⟩ := hrep t0 ht0
      refine lt_of_le_of_lt ?_ hb
      rw [hw, ← pathSumHat_eq]
      exact (EReal.coe_le_coe_iff.2 (hUhat j)).trans (le_iSup (fun r : ℕ => ((Uhat E R C r : ℝ) : EReal)) j.length)

end Det

lemma unbounded_of_freq {E : ℕ → ℝ} (hE : ∀ k, 0 < E k) (hf : ∃ᶠ k in atTop, 1 < E k) :
    ∀ M : ℝ, ∃ k, arrival E k < M := by
  have hc : ∀ c : ℕ, ∃ k, (c : ℝ) ≤ ∑ j ∈ Finset.Icc 1 k, E j := by
    intro c
    induction c with
    | zero => exact ⟨0, by simp⟩
    | succ c ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨k', h1, hk'⟩ := (hf.and_eventually (eventually_gt_atTop k)).exists
      refine ⟨k', ?_⟩
      have hsub : insert k' (Finset.Icc 1 k) ⊆ Finset.Icc 1 k' := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_Icc] at hx ⊢
        omega
      have hnot : k' ∉ Finset.Icc 1 k := by simp; omega
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => (hE x).le)
      rw [Finset.sum_insert hnot] at this
      push_cast
      linarith
  intro M
  obtain ⟨k, hk⟩ := hc (⌈-M⌉₊ + 1)
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
    linarith [Nat.cast_nonneg (α := ℝ) ⌈-M⌉₊]
  refine ⟨k, ?_⟩
  unfold arrival
  rw [if_neg hk0]
  have := Nat.le_ceil (-M)
  push_cast at hk
  linarith

end SQE61

open SQE61 in
theorem solution {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam)
    (Bm : Measure (Fin m → ℝ)) [IsProbabilityMeasure Bm] (hBm : ∀ᵐ x ∂Bm, ∀ i, 0 ≤ x i)
    {n : ℕ} (hn : m ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → Ω → ℝ) (R : ℕ → Ω → (Fin m → ℕ)) (C : ℕ → Ω → (Fin m → ℝ))
    (hsys : IsSyncSystem P m n lam Bm E R C) :
    ∀ᵐ ω ∂P,
      AntitoneOn (fun t0 => waitT (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) t0) (Set.Iio 0) ∧
      Tendsto (fun t0 => ((waitT (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) t0 : ℝ) : EReal)) atBot
        (𝓝 (⨆ r : ℕ, ((Uhat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) r : ℝ) : EReal))) := by
  filter_upwards [ae_good hm hn hlam hsys] with ω ⟨hE, hf, hS, hsrv⟩
  refine det_main hm hE (unbounded_of_freq hE hf) ?_
  intro k i
  have hlt : R k ω i < n := (hS k).2 i
  obtain ⟨k', h1, h2⟩ := ((hsrv _ hlt).and_eventually (eventually_gt_atTop k)).exists
  exact ⟨k', h2, h1⟩
