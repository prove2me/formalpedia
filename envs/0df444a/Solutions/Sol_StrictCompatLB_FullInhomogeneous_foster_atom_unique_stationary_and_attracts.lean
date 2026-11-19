-- Prove2me | solution 1 for StrictCompatLB.FullInhomogeneous.foster_atom_unique_stationary_and_attracts
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-18T20:28:59.683816+00:00
-- url     : https://prove2.me/submissions/61995a88-b222-474c-a251-14e5e0edb7db

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_CountableChain
import Definitions.Def_StrictCompatLB_FullInhomogeneous_UniformizedLaw
import Definitions.Def_DurrettProbability_MarkovChain
import Theorems.Thm_DurrettProbability_markov_convergence

set_option autoImplicit false



open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SC9aK4P

open StrictCompatLB.MeanField StrictCompatLB.FullInhomogeneous

/-! K4P (Poissonisation): l1 convergence of the discrete n-step laws to `π` implies
`AttractsAllStates` for the uniformised continuous-time chain. Helper lemmas `Kn`, `marg`,
`marg1`, `meas_ec` copied from our proved child K9 of 77ae612d. -/

section Gen

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] [DecidableEq S]

/-- The `n`-step kernel, in `ℝ≥0∞`. -/
noncomputable def Kn (K : S → S → ℝ) : ℕ → S → S → ℝ≥0∞
  | 0 => fun a b => if b = a then 1 else 0
  | n + 1 => fun a b => ∑' y, Kn K n a y * ENNReal.ofReal (K y b)

/-- `b` bounds every `a` with `τ 0 + ⋯ + τ (a-1) ≤ t`. -/
def ub (t : ℝ) (s : ℕ → ℝ) (b : ℕ) : Prop :=
  ∀ a : ℕ, (∑ k ∈ Finset.range a, s k ≤ t) → a ≤ b

lemma ec_eq_iff (s : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    epochCount s t = n ↔ ((∃ b, ub t s b) ∧ ub t s n ∧ ∀ m < n, ¬ ub t s m) ∨
      (¬ (∃ b, ub t s b) ∧ n = 0) := by
  classical
  unfold epochCount
  by_cases h : ∃ b, ub t s b
  · have h' : ∃ b, ∀ a ∈ {n : ℕ | ∑ k ∈ Finset.range n, s k ≤ t}, a ≤ b := h
    rw [Nat.sSup_def h', Nat.find_eq_iff]
    exact ⟨fun hx => Or.inl ⟨h, hx⟩, fun hx => hx.elim (fun hx => hx.2) (fun hx => absurd h hx.1)⟩
  · have h' : ¬ BddAbove {n : ℕ | ∑ k ∈ Finset.range n, s k ≤ t} := by
      rw [bddAbove_def]; exact h
    rw [Nat.sSup_of_not_bddAbove h']
    exact ⟨fun hx => Or.inr ⟨h, hx.symm⟩,
      fun hx => hx.elim (fun hx => absurd hx.1 h) (fun hx => hx.2.symm)⟩

lemma meas_le (t : ℝ) (a : ℕ) :
    Measurable (fun s : ℕ → ℝ => ∑ k ∈ Finset.range a, s k ≤ t) :=
  measurableSet_setOf.1
    (measurableSet_le (Finset.measurable_sum _ (fun k _ => measurable_pi_apply k)) measurable_const)

lemma meas_ub (t : ℝ) (b : ℕ) : Measurable (fun s => ub t s b) := by
  unfold ub
  exact Measurable.forall fun a => (meas_le t a).imp measurable_const

lemma meas_ec (t : ℝ) (n : ℕ) : MeasurableSet {s : ℕ → ℝ | epochCount s t = n} := by
  have : {s : ℕ → ℝ | epochCount s t = n} = {s | ((∃ b, ub t s b) ∧ ub t s n ∧
      ∀ m < n, ¬ ub t s m) ∨ (¬ (∃ b, ub t s b) ∧ n = 0)} := by
    ext s; exact ec_eq_iff s t n
  rw [this]
  refine measurableSet_setOf.2 (Measurable.or ?_ ?_)
  · exact (Measurable.exists fun b => meas_ub t b).and ((meas_ub t n).and
      (Measurable.forall fun m => measurable_const.imp (meas_ub t m).not))
  · exact (Measurable.exists fun b => meas_ub t b).not.and measurable_const


lemma marg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {K : S → S → ℝ} {rate : ℝ} {z₀ : S}
    {Y : ℕ → Ω → S} {τ : ℕ → Ω → ℝ} (hU : IsUniformizedProcess P K rate z₀ Y τ)
    (hK : IsStochasticKernel K) :
    ∀ k n (w : ℕ → S), k ≤ n → P {ω | ∀ j, k ≤ j → j ≤ n → Y j ω = w j} =
      Kn K k z₀ (w k) * ∏ j ∈ Finset.Ico k n, ENNReal.ofReal (K (w j) (w (j + 1))) := by
  intro k
  induction k with
  | zero =>
    intro n w _
    have hs : {ω | ∀ j, 0 ≤ j → j ≤ n → Y j ω = w j} = {ω | ∀ j ≤ n, Y j ω = w j} := by
      ext ω; simp
    rw [hs, hU.2.2.1 n w,
      ENNReal.ofReal_mul (show (0:ℝ) ≤ (if w 0 = z₀ then 1 else 0) by split_ifs <;> norm_num),
      ENNReal.ofReal_prod_of_nonneg (fun j _ => hK.1 (w j) (w (j + 1))), ← Finset.range_eq_Ico]
    congr 1
    show ENNReal.ofReal (if w 0 = z₀ then 1 else 0) = if w 0 = z₀ then 1 else 0
    split_ifs <;> simp
  | succ k ih =>
    intro n w hkn
    have hmeas : ∀ v : ℕ → S, MeasurableSet {ω | ∀ j, k ≤ j → j ≤ n → Y j ω = v j} := fun v =>
      measurableSet_setOf.2 (Measurable.forall fun j => measurable_const.imp
        (measurable_const.imp (measurableSet_setOf.1 ((hU.2.1 j) (measurableSet_singleton (v j))))))
    have hset : {ω | ∀ j, k + 1 ≤ j → j ≤ n → Y j ω = w j} =
        ⋃ y : S, {ω | ∀ j, k ≤ j → j ≤ n → Y j ω = Function.update w k y j} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro h
        refine ⟨Y k ω, fun j hj1 hj2 => ?_⟩
        rcases Nat.eq_or_lt_of_le hj1 with h' | h'
        · subst h'; simp
        · rw [Function.update_of_ne (show j ≠ k by omega)]; exact h j h' hj2
      · rintro ⟨y, h⟩ j hj1 hj2
        have := h j (by omega) hj2
        rwa [Function.update_of_ne (show j ≠ k by omega)] at this
    have hdisj : Pairwise (Function.onFun Disjoint fun y : S =>
        {ω | ∀ j, k ≤ j → j ≤ n → Y j ω = Function.update w k y j}) := by
      intro y y' hyy'
      refine Set.disjoint_left.2 fun ω h1 h2 => hyy' ?_
      have a1 := h1 k le_rfl (by omega)
      have a2 := h2 k le_rfl (by omega)
      simp only [Function.update_self] at a1 a2
      rw [← a1, ← a2]
    rw [hset, measure_iUnion hdisj (fun y => hmeas _)]
    simp_rw [ih n _ (by omega : k ≤ n)]
    simp_rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : k < n)]
    have hrest : ∀ y : S, ∏ j ∈ Finset.Ico (k + 1) n,
        ENNReal.ofReal (K (Function.update w k y j) (Function.update w k y (j + 1))) =
        ∏ j ∈ Finset.Ico (k + 1) n, ENNReal.ofReal (K (w j) (w (j + 1))) := by
      intro y
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Finset.mem_Ico] at hj
      rw [Function.update_of_ne (show j ≠ k by omega), Function.update_of_ne (show j + 1 ≠ k by omega)]
    simp_rw [hrest, Function.update_self, Function.update_of_ne (show k + 1 ≠ k by omega)]
    rw [show Kn K (k + 1) z₀ (w (k + 1)) = ∑' y, Kn K k z₀ y * ENNReal.ofReal (K y (w (k + 1)))
      from rfl, ← ENNReal.tsum_mul_right]
    congr 1
    funext y
    ring

lemma marg1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {K : S → S → ℝ} {rate : ℝ} {z₀ : S}
    {Y : ℕ → Ω → S} {τ : ℕ → Ω → ℝ} (hU : IsUniformizedProcess P K rate z₀ Y τ)
    (hK : IsStochasticKernel K) (n : ℕ) (z' : S) : P {ω | Y n ω = z'} = Kn K n z₀ z' := by
  have h := marg hU hK n n (fun _ => z') le_rfl
  rw [Finset.Ico_self, Finset.prod_empty, mul_one] at h
  rw [← h]
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h j h1 h2; rw [show j = n by omega]; exact h
  · intro h; exact h n le_rfl le_rfl

lemma Kn_row (K : S → S → ℝ) (hK : IsStochasticKernel K) :
    ∀ n a, ∑' b, Kn K n a b = 1 := by
  intro n
  induction n with
  | zero =>
    intro a
    simp only [Kn]
    rw [tsum_eq_single a (fun b hb => by simp [hb])]
    simp
  | succ n ih =>
    intro a
    simp only [Kn]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    have hrow : ∀ y, ∑' b, ENNReal.ofReal (K y b) = 1 := fun y => by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun b => hK.1 y b) (hK.2 y).summable, (hK.2 y).tsum_eq,
        ENNReal.ofReal_one]
    simp_rw [hrow, mul_one, ih]

lemma Kn_le_one (K : S → S → ℝ) (hK : IsStochasticKernel K) (n : ℕ) (a b : S) :
    Kn K n a b ≤ 1 := by
  rw [← Kn_row K hK n a]; exact ENNReal.le_tsum b

lemma Kn_ne_top (K : S → S → ℝ) (hK : IsStochasticKernel K) (n : ℕ) (a b : S) :
    Kn K n a b ≠ ⊤ := ((Kn_le_one K hK n a b).trans_lt ENNReal.one_lt_top).ne

lemma stepProb_eq (K : S → S → ℝ) (hK : IsStochasticKernel K) :
    ∀ n a b, stepProb K n a b = (Kn K n a b).toReal := by
  intro n
  induction n with
  | zero =>
    intro a b
    simp only [stepProb, Kn]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  | succ n ih =>
    intro a b
    simp only [stepProb, Kn]
    rw [ENNReal.tsum_toReal_eq (fun y => ENNReal.mul_ne_top (Kn_ne_top K hK n a y)
      ENNReal.ofReal_ne_top)]
    refine tsum_congr fun y => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hK.1 y b), ih]

lemma uproc_of_law {K : S → S → ℝ} {rate : ℝ} {z : S} {P : Measure (ChainSample S)}
    (hP : IsUniformizedLaw P K rate (fun z' => if z' = z then 1 else 0)) :
    IsUniformizedProcess P K rate z (fun n ω => ω.1 n) (fun k ω => ω.2 k) := by
  obtain ⟨h1, _, hcyl, hiid, hexp, hind, _⟩ := hP
  exact ⟨h1, fun n => (measurable_pi_apply n).comp measurable_fst, fun n zs => hcyl n zs,
    fun k => (measurable_pi_apply k).comp measurable_snd, hiid, hexp, hind⟩

end Gen

lemma absdiff (u v : ℝ≥0∞) (hu : u ≠ ⊤) (hv : v ≠ ⊤) :
    ENNReal.ofReal |u.toReal - v.toReal| = (u - v) + (v - u) := by
  rcases le_total u v with h | h
  · rw [tsub_eq_zero_of_le h, zero_add, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 (ENNReal.toReal_mono hv h)),
      ← ENNReal.toReal_sub_of_le h hv, ENNReal.ofReal_toReal (ENNReal.sub_ne_top hv)]
  · rw [tsub_eq_zero_of_le h, add_zero, abs_of_nonneg (sub_nonneg.2 (ENNReal.toReal_mono hu h)),
      ← ENNReal.toReal_sub_of_le h hu, ENNReal.ofReal_toReal (ENNReal.sub_ne_top hu)]

lemma sub_tsum_le (a b q : ℕ → ℝ≥0∞) :
    (∑' n, a n * q n) - (∑' n, b n * q n) ≤ ∑' n, (a n - b n) * q n := by
  rw [tsub_le_iff_right, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun n => by rw [← add_mul]; gcongr; exact le_tsub_add

lemma absdiff_le (a q : ℕ → ℝ≥0∞) (c : ℝ≥0∞) (hq : ∑' n, q n = 1)
    (hu : ∑' n, a n * q n ≠ ⊤) (hc : c ≠ ⊤) :
    ENNReal.ofReal |(∑' n, a n * q n).toReal - c.toReal| ≤ ∑' n, ((a n - c) + (c - a n)) * q n := by
  have hv : c = ∑' n, c * q n := by rw [ENNReal.tsum_mul_left, hq, mul_one]
  rw [absdiff _ _ hu hc]
  calc _ ≤ ∑' n, (a n - c) * q n + ∑' n, (c - a n) * q n := by
        refine add_le_add ?_ ?_
        · conv_lhs => rw [hv]
          exact sub_tsum_le a (fun _ => c) q
        · conv_lhs => rw [hv]
          exact sub_tsum_le (fun _ => c) a q
    _ = _ := by
        rw [← ENNReal.tsum_add]; exact tsum_congr fun n => (add_mul _ _ _).symm

lemma ofReal_tsum_le' {α : Type*} (f : α → ℝ) (hf : ∀ z, 0 ≤ f z) :
    ENNReal.ofReal (∑' z, f z) ≤ ∑' z, ENNReal.ofReal (f z) := by
  by_cases h : Summable f
  · rw [ENNReal.ofReal_tsum_of_nonneg hf h]
  · rw [tsum_eq_zero_of_not_summable h, ENNReal.ofReal_zero]; exact bot_le

theorem k4p {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
    [DecidableEq S] (K : S → S → ℝ) (hK : IsStochasticKernel K) (π : S → ℝ) (hπ : IsProbVec π)
    (rate : ℝ)
    (hconv : ∀ z, Tendsto (fun n => ∑' z', |stepProb K n z z' - π z'|) atTop (𝓝 0)) :
    AttractsAllStates K rate π := by
  intro z P hP
  have hU := uproc_of_law hP
  haveI := hU.1
  obtain ⟨_, _, _, _, _, hind, hae⟩ := hP
  have hsnd : Measurable (fun ω : ChainSample S => ω.2) := measurable_snd
  have hfst : Measurable (fun ω : ChainSample S => ω.1) := measurable_fst
  have hecm : ∀ t n, MeasurableSet {ω : ChainSample S | epochCount ω.2 t = n} :=
    fun t n => hsnd (meas_ec t n)
  have hA : ∀ n z', P {ω : ChainSample S | ω.1 n = z'} = ENNReal.ofReal (stepProb K n z z') := by
    intro n z'
    rw [show P {ω : ChainSample S | ω.1 n = z'} = Kn K n z z' from marg1 hU hK n z',
      stepProb_eq K hK, ENNReal.ofReal_toReal (Kn_ne_top K hK n z z')]
  have hqsum : ∀ t, ∑' n, P {ω : ChainSample S | epochCount ω.2 t = n} = 1 := by
    intro t
    have h := measure_iUnion (μ := P)
      (f := fun n : ℕ => {ω : ChainSample S | epochCount ω.2 t = n})
      (fun n m hnm => Set.disjoint_left.2 fun ω (h1 : epochCount ω.2 t = n)
        (h2 : epochCount ω.2 t = m) => hnm (h1.symm.trans h2))
      (fun n => hecm t n)
    have hu : (⋃ n : ℕ, {ω : ChainSample S | epochCount ω.2 t = n}) = Set.univ := by
      ext ω; simp
    rw [hu, measure_univ] at h
    exact h.symm
  have hform : ∀ t z', P {ω : ChainSample S | taggedState ω t = z'} =
      ∑' n, ENNReal.ofReal (stepProb K n z z') * P {ω : ChainSample S | epochCount ω.2 t = n} := by
    intro t z'
    have hset : {ω : ChainSample S | taggedState ω t = z'} = ⋃ n : ℕ,
        ((fun ω : ChainSample S => ω.1) ⁻¹' {y : ℕ → S | y n = z'} ∩
          (fun ω : ChainSample S => ω.2) ⁻¹' {s : ℕ → ℝ | epochCount s t = n}) := by
      ext ω
      simp only [taggedState, jumpPath, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_preimage]
      constructor
      · intro h; exact ⟨_, h, rfl⟩
      · rintro ⟨n, h, hn⟩; rw [hn]; exact h
    rw [hset, measure_iUnion]
    · refine tsum_congr fun n => ?_
      rw [hind.measure_inter_preimage_eq_mul {y : ℕ → S | y n = z'}
        {s : ℕ → ℝ | epochCount s t = n} ((measurableSet_singleton z').preimage (measurable_pi_apply n))
        (meas_ec t n), ← hA n z']
      rfl
    · intro n m hnm
      refine Set.disjoint_left.2 fun ω h1 h2 => hnm ?_
      have e1 : epochCount ω.2 t = n := h1.2
      have e2 : epochCount ω.2 t = m := h2.2
      exact e1.symm.trans e2
    · intro n
      exact (hfst ((measurableSet_singleton z').preimage (measurable_pi_apply n))).inter (hecm t n)
  have hbad : P {ω : ChainSample S |
      ¬ Tendsto (fun n => ∑ k ∈ Finset.range n, ω.2 k) atTop atTop} = 0 :=
    ae_iff.1 (hae.mono fun ω h => h.2)
  have hqto : ∀ n, Tendsto (fun t => P {ω : ChainSample S | epochCount ω.2 t = n})
      atTop (𝓝 0) := by
    intro n
    have hsm : ∀ t : ℝ, MeasurableSet {ω : ChainSample S | t < ∑ k ∈ Finset.range (n + 1), ω.2 k} :=
      fun t => measurableSet_lt measurable_const
        (Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).comp measurable_snd)
    have hanti : Antitone (fun t : ℝ =>
        {ω : ChainSample S | t < ∑ k ∈ Finset.range (n + 1), ω.2 k}) :=
      fun t1 t2 h ω hω => lt_of_le_of_lt h hω
    have hinter : (⋂ t : ℝ, {ω : ChainSample S | t < ∑ k ∈ Finset.range (n + 1), ω.2 k}) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨∑ k ∈ Finset.range (n + 1), ω.2 k, lt_irrefl _⟩
    have h1 : Tendsto (fun t : ℝ =>
        P {ω : ChainSample S | t < ∑ k ∈ Finset.range (n + 1), ω.2 k}) atTop (𝓝 0) := by
      have := tendsto_measure_iInter_atTop (μ := P) (fun t => (hsm t).nullMeasurableSet) hanti
        ⟨0, measure_ne_top P _⟩
      rw [hinter, measure_empty] at this
      exact this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
      (fun _ => bot_le) ?_
    intro t
    calc P {ω : ChainSample S | epochCount ω.2 t = n}
        ≤ P ({ω : ChainSample S | t < ∑ k ∈ Finset.range (n + 1), ω.2 k} ∪
            {ω : ChainSample S |
              ¬ Tendsto (fun n => ∑ k ∈ Finset.range n, ω.2 k) atTop atTop}) := by
          refine measure_mono fun ω hω => ?_
          by_cases hT : Tendsto (fun n => ∑ k ∈ Finset.range n, ω.2 k) atTop atTop
          · left
            show t < _
            by_contra hle
            push_neg at hle
            have hbdd : BddAbove {m : ℕ | ∑ k ∈ Finset.range m, ω.2 k ≤ t} := by
              obtain ⟨M, hM⟩ := eventually_atTop.1 (tendsto_atTop.1 hT (t + 1))
              refine ⟨M, fun m hm => ?_⟩
              by_contra hlt
              push_neg at hlt
              have h3 := hM m hlt.le
              have hm' : ∑ k ∈ Finset.range m, ω.2 k ≤ t := hm
              linarith
            have h4 := le_csSup hbdd
              (show n + 1 ∈ {m : ℕ | ∑ k ∈ Finset.range m, ω.2 k ≤ t} from hle)
            have hq : sSup {m : ℕ | ∑ k ∈ Finset.range m, ω.2 k ≤ t} = n := hω
            rw [hq] at h4
            omega
          · right; exact hT
      _ ≤ _ := measure_union_le _ _
      _ = _ := by rw [hbad, add_zero]
  have hspn : ∀ n z', 0 ≤ stepProb K n z z' := fun n z' => by
    rw [stepProb_eq K hK]; exact ENNReal.toReal_nonneg
  have hsp : ∀ n, Summable (fun z' => stepProb K n z z') := fun n => by
    simp_rw [stepProb_eq K hK]
    exact ENNReal.summable_toReal (by rw [Kn_row K hK n z]; exact ENNReal.one_ne_top)
  have hsp1 : ∀ n, ∑' z', stepProb K n z z' = 1 := fun n => by
    simp_rw [stepProb_eq K hK]
    rw [← ENNReal.tsum_toReal_eq (fun z' => Kn_ne_top K hK n z z'), Kn_row K hK n z,
      ENNReal.toReal_one]
  have hsumm : ∀ n, Summable (fun z' => |stepProb K n z z' - π z'|) := fun n =>
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
      (fun z' => abs_le.2 ⟨by linarith [hspn n z', hπ.1 z'], by linarith [hspn n z', hπ.1 z']⟩)
      ((hsp n).add hπ.2.summable)
  have he2 : ∀ n, ∑' z', |stepProb K n z z' - π z'| ≤ 2 := fun n => by
    calc _ ≤ ∑' z', (stepProb K n z z' + π z') :=
          (hsumm n).tsum_le_tsum (fun z' => abs_le.2 ⟨by linarith [hspn n z', hπ.1 z'],
            by linarith [hspn n z', hπ.1 z']⟩) ((hsp n).add hπ.2.summable)
      _ = 2 := by rw [(hsp n).tsum_add hπ.2.summable, hsp1, hπ.2.tsum_eq]; norm_num
  have hD : ∀ n, ∑' z', ENNReal.ofReal |stepProb K n z z' - π z'| =
      ENNReal.ofReal (∑' z', |stepProb K n z z' - π z'|) := fun n =>
    (ENNReal.ofReal_tsum_of_nonneg (fun _ => abs_nonneg _) (hsumm n)).symm
  have hE : Tendsto (fun n => ENNReal.ofReal (∑' z', |stepProb K n z z' - π z'|)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]; exact ENNReal.tendsto_ofReal (hconv z)
  have hGt : ∀ t, ∑' n, ENNReal.ofReal (∑' z', |stepProb K n z z' - π z'|) *
      P {ω : ChainSample S | epochCount ω.2 t = n} ≤ 2 := fun t => by
    calc _ ≤ ∑' n, 2 * P {ω : ChainSample S | epochCount ω.2 t = n} :=
          ENNReal.tsum_le_tsum fun n => by
            gcongr; exact ENNReal.ofReal_le_of_le_toReal (by simpa using he2 n)
      _ = 2 := by rw [ENNReal.tsum_mul_left, hqsum t, mul_one]
  have hG : Tendsto (fun t => ∑' n, ENNReal.ofReal (∑' z', |stepProb K n z z' - π z'|) *
      P {ω : ChainSample S | epochCount ω.2 t = n}) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
    obtain ⟨n0, hn0⟩ := eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 hE) (ε / 2) hε2)
    have hfin : Tendsto (fun t => 2 * ∑ n ∈ Finset.range n0,
        P {ω : ChainSample S | epochCount ω.2 t = n}) atTop (𝓝 0) := by
      have : Tendsto (fun t => ∑ n ∈ Finset.range n0,
          P {ω : ChainSample S | epochCount ω.2 t = n}) atTop (𝓝 0) := by
        simpa using tendsto_finsetSum (Finset.range n0) (fun n _ => hqto n)
      simpa using ENNReal.Tendsto.const_mul this (Or.inr ENNReal.ofNat_ne_top)
    filter_upwards [(ENNReal.tendsto_nhds_zero.1 hfin) (ε / 2) hε2] with t ht
    calc _ ≤ ∑' n, ((if n < n0 then 2 * P {ω : ChainSample S | epochCount ω.2 t = n} else 0) +
            ε / 2 * P {ω : ChainSample S | epochCount ω.2 t = n}) := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          by_cases hn : n < n0
          · rw [if_pos hn]
            refine le_trans ?_ le_self_add
            gcongr; exact ENNReal.ofReal_le_of_le_toReal (by simpa using he2 n)
          · rw [if_neg hn, zero_add]
            gcongr; exact hn0 n (not_lt.1 hn)
      _ = 2 * ∑ n ∈ Finset.range n0, P {ω : ChainSample S | epochCount ω.2 t = n} + ε / 2 := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hqsum t, mul_one, Finset.mul_sum]
          congr 1
          rw [tsum_eq_sum (s := Finset.range n0) (fun n hn => by
            rw [Finset.mem_range] at hn; rw [if_neg hn])]
          exact Finset.sum_congr rfl fun n hn => if_pos (Finset.mem_range.1 hn)
      _ ≤ ε / 2 + ε / 2 := add_le_add ht le_rfl
      _ = ε := ENNReal.add_halves ε
  have hz' : ∀ t z', ENNReal.ofReal |(P {ω : ChainSample S | taggedState ω t = z'}).toReal - π z'|
      ≤ ∑' n, ENNReal.ofReal |stepProb K n z z' - π z'| *
        P {ω : ChainSample S | epochCount ω.2 t = n} := by
    intro t z'
    have h1 := absdiff_le (fun n => ENNReal.ofReal (stepProb K n z z'))
      (fun n => P {ω : ChainSample S | epochCount ω.2 t = n}) (ENNReal.ofReal (π z')) (hqsum t)
      (by beta_reduce; rw [← hform t z']; exact measure_ne_top _ _) ENNReal.ofReal_ne_top
    beta_reduce at h1
    rw [← hform t z', ENNReal.toReal_ofReal (hπ.1 z')] at h1
    refine h1.trans (le_of_eq (tsum_congr fun n => ?_))
    have h2 := absdiff (ENNReal.ofReal (stepProb K n z z')) (ENNReal.ofReal (π z'))
      ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal (hspn n z'), ENNReal.toReal_ofReal (hπ.1 z')] at h2
    rw [h2]
  have hpt : ∀ t, ∑' z', |(P {ω : ChainSample S | taggedState ω t = z'}).toReal - π z'| ≤
      (∑' n, ENNReal.ofReal (∑' z', |stepProb K n z z' - π z'|) *
        P {ω : ChainSample S | epochCount ω.2 t = n}).toReal := by
    intro t
    rw [← ENNReal.toReal_ofReal (tsum_nonneg fun _ => abs_nonneg _)]
    refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofNat_ne_top (hGt t)) ?_
    refine (ofReal_tsum_le' _ fun _ => abs_nonneg _).trans ?_
    calc _ ≤ ∑' z', ∑' n, ENNReal.ofReal |stepProb K n z z' - π z'| *
            P {ω : ChainSample S | epochCount ω.2 t = n} := ENNReal.tsum_le_tsum fun z' => hz' t z'
      _ = _ := by
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun n => ?_
          rw [ENNReal.tsum_mul_right, hD n]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun t => tsum_nonneg fun _ => abs_nonneg _) hpt
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hG

end SC9aK4P




open MeasureTheory Filter Topology
open scoped ENNReal
open StrictCompatLB.MeanField

namespace SC9aK4H

/-- K4H (Foster drift off a finite set + an atom accessible from it => the atom is hit with
probability one from every state; Meyn-Tweedie Thm 8.4.3 / 11.3.4 analytic form). The mass of
the taboo kernel `Q a b = K a b * 1{b ≠ z₀}` after `n` steps is `P_x(no visit to z₀ at times 1..n)`. -/
def K4HStmt : Prop :=
  ∀ {S : Type} [DecidableEq S] [Countable S]
    (K : S → S → ℝ), IsStochasticKernel K →
    ∀ (V : S → ℝ), (∀ z, 0 ≤ V z) → (∀ z, Summable (fun z' => K z z' * V z')) →
    ∀ (C : Set S), C.Finite → ∀ b : ℝ,
    (∀ z, oneStepDrift K V z ≤ -1 + b * C.indicator (fun _ => (1 : ℝ)) z) →
    ∀ z₀ : S, 0 < K z₀ z₀ → (∀ z ∈ C, ∃ n, 0 < stepProb K n z z₀) →
    ∀ x : S, Tendsto (fun n => ∑' y, stepProb (fun a b => if b = z₀ then 0 else K a b) n x y)
      atTop (𝓝 0)

section Gen

variable {S : Type} [DecidableEq S] [Countable S]

/-- `n`-step kernel of an `ℝ≥0∞` kernel (right recursion, like `stepProb`). -/
noncomputable def KE (P : S → S → ℝ≥0∞) : ℕ → S → S → ℝ≥0∞
  | 0 => fun a b => if a = b then 1 else 0
  | n + 1 => fun a b => ∑' y, KE P n a y * P y b

/-- The operator `f ↦ P f`. -/
noncomputable def op (P : S → S → ℝ≥0∞) (f : S → ℝ≥0∞) : S → ℝ≥0∞ :=
  fun x => ∑' w, P x w * f w

lemma op_mono (P : S → S → ℝ≥0∞) : Monotone (op P) := by
  intro f g hfg x
  exact ENNReal.tsum_le_tsum fun w => mul_le_mul_right (hfg w) _

lemma op_one_le (P : S → S → ℝ≥0∞) (hP : ∀ a, ∑' b, P a b ≤ 1) : op P 1 ≤ 1 := by
  intro x
  simpa [op] using hP x

lemma iter_one_le (P : S → S → ℝ≥0∞) (hP : ∀ a, ∑' b, P a b ≤ 1) :
    ∀ n, (op P)^[n] 1 ≤ 1 := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (op_mono P ih).trans (op_one_le P hP)

lemma iter_ge (P : S → S → ℝ≥0∞) (f : S → ℝ≥0∞) (hf : f ≤ op P f) :
    ∀ n, f ≤ (op P)^[n] f := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hf.trans (op_mono P ih)

lemma op_const_mul (P : S → S → ℝ≥0∞) (c : ℝ≥0∞) (f : S → ℝ≥0∞) :
    op P (fun w => c * f w) = fun x => c * op P f x := by
  funext x
  simp only [op]
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun w => by ring

lemma iter_const_mul (P : S → S → ℝ≥0∞) (c : ℝ≥0∞) (f : S → ℝ≥0∞) (n : ℕ) :
    (op P)^[n] (fun w => c * f w) = fun x => c * (op P)^[n] f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, op_const_mul]

lemma KE_op (P : S → S → ℝ≥0∞) :
    ∀ n (f : S → ℝ≥0∞) x, ∑' b, KE P n x b * f b = (op P)^[n] f x := by
  intro n
  induction n with
  | zero =>
    intro f x
    simp only [KE, Function.iterate_zero, id]
    rw [tsum_eq_single x (fun b hb => by simp [Ne.symm hb])]
    simp
  | succ n ih =>
    intro f x
    simp only [KE]
    simp_rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    rw [Function.iterate_succ_apply]
    exact ih (op P f) x

lemma KE_op1 (P : S → S → ℝ≥0∞) (n : ℕ) (x : S) :
    ∑' b, KE P n x b = (op P)^[n] 1 x := by
  simpa using KE_op P n 1 x

lemma KE_row_le (P : S → S → ℝ≥0∞) (hP : ∀ a, ∑' b, P a b ≤ 1) :
    ∀ n a, ∑' b, KE P n a b ≤ 1 := by
  intro n a
  rw [KE_op1]
  exact iter_one_le P hP n a

lemma KE_ne_top (P : S → S → ℝ≥0∞) (hP : ∀ a, ∑' b, P a b ≤ 1) (n : ℕ) (a b : S) :
    KE P n a b ≠ ⊤ :=
  ((ENNReal.le_tsum b).trans (KE_row_le P hP n a) |>.trans_lt ENNReal.one_lt_top).ne

lemma KE_mono (P P' : S → S → ℝ≥0∞) (h : ∀ a b, P a b ≤ P' a b) :
    ∀ n a b, KE P n a b ≤ KE P' n a b := by
  intro n
  induction n with
  | zero => intro a b; exact le_rfl
  | succ n ih =>
    intro a b
    exact ENNReal.tsum_le_tsum fun y => mul_le_mul' (ih a y) (h y b)

lemma stepProb_eq' (K : S → S → ℝ) (h0 : ∀ a b, 0 ≤ K a b)
    (hrow : ∀ a, ∑' b, ENNReal.ofReal (K a b) ≤ 1) :
    ∀ n a b, stepProb K n a b = (KE (fun a b => ENNReal.ofReal (K a b)) n a b).toReal := by
  intro n
  induction n with
  | zero =>
    intro a b
    simp only [stepProb, KE]
    split_ifs <;> simp
  | succ n ih =>
    intro a b
    simp only [stepProb, KE]
    rw [ENNReal.tsum_toReal_eq (fun y => ENNReal.mul_ne_top (KE_ne_top _ hrow n a y)
      ENNReal.ofReal_ne_top)]
    refine tsum_congr fun y => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (h0 y b), ih]

/-- Decreasing limits pass under a finite-mass sum. -/
lemma iInf_tsum_le (a : S → ℝ≥0∞) (ha : ∀ w, a w ≠ ⊤) (g : ℕ → S → ℝ≥0∞) (hg : Antitone g)
    (hfin : ∑' w, a w * g 0 w ≠ ⊤) :
    ⨅ n, ∑' w, a w * g n w ≤ ∑' w, a w * ⨅ n, g n w := by
  letI : MeasurableSpace S := ⊤
  haveI : MeasurableSingletonClass S := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have key := lintegral_iInf (μ := Measure.count) (f := fun n w => a w * g n w)
    (fun n => measurable_from_top) (fun m n hmn w => mul_le_mul_right (hg hmn w) _)
    (by rw [lintegral_count]; exact hfin)
  simp only [lintegral_count] at key
  rw [← key]
  refine ENNReal.tsum_le_tsum fun w => ?_
  by_cases ha0 : a w = 0
  · simp [ha0]
  · rw [ENNReal.mul_iInf_of_ne ha0 (ha w)]

end Gen

theorem k4h : K4HStmt := by
  intro S _ _ K hK V hV0 hVs C hC b hdrift z₀ hz₀ hacc x
  classical
  set Kk : S → S → ℝ≥0∞ := fun a b => ENNReal.ofReal (K a b) with hKk
  set P : S → S → ℝ≥0∞ := fun a b => if b = z₀ then 0 else Kk a b with hPdef
  set R : S → S → ℝ≥0∞ := fun a b => if b ∈ C then 0 else Kk a b with hRdef
  set VE : S → ℝ≥0∞ := fun z => ENNReal.ofReal (V z) with hVE
  have hKrow : ∀ a, ∑' b, Kk a b ≤ 1 := fun a => by
    rw [hKk, ← ENNReal.ofReal_tsum_of_nonneg (fun b => hK.1 a b) (hK.2 a).summable,
      (hK.2 a).tsum_eq, ENNReal.ofReal_one]
  have hPle : ∀ a b, P a b ≤ Kk a b := fun a b => by
    simp only [hPdef]; split_ifs <;> simp
  have hRle : ∀ a b, R a b ≤ Kk a b := fun a b => by
    simp only [hRdef]; split_ifs <;> simp
  have hProw : ∀ a, ∑' b, P a b ≤ 1 := fun a =>
    (ENNReal.tsum_le_tsum (hPle a)).trans (hKrow a)
  have hRrow : ∀ a, ∑' b, R a b ≤ 1 := fun a =>
    (ENNReal.tsum_le_tsum (hRle a)).trans (hKrow a)
  have hKV : ∀ z, ∑' w, Kk z w * VE w = ENNReal.ofReal (∑' w, K z w * V w) := fun z => by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun w => mul_nonneg (hK.1 z w) (hV0 w)) (hVs z)]
    refine tsum_congr fun w => ?_
    rw [ENNReal.ofReal_mul (hK.1 z w)]
  have hfin : ∀ z, ∑' w, Kk z w * VE w ≠ ⊤ := fun z => by
    rw [hKV]; exact ENNReal.ofReal_ne_top
  have hfoster : ∀ y, y ∉ C → 1 + ∑' w, Kk y w * VE w ≤ VE y := by
    intro y hy
    have hd := hdrift y
    simp only [oneStepDrift, kexp, Set.indicator_of_notMem hy, mul_zero, add_zero] at hd
    rw [hKV, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (tsum_nonneg fun w => mul_nonneg (hK.1 y w) (hV0 w))]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- Foster: expected time spent off `C`
  have hF : ∀ n : ℕ, ∀ y, y ∉ C →
      (n : ℝ≥0∞) * (op R)^[n] 1 y + (op R)^[n] VE y ≤ VE y := by
    intro n
    induction n with
    | zero => intro y _; simp
    | succ n ih =>
      intro y hy
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp only [op]
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      calc ∑' w, (((n + 1 : ℕ) : ℝ≥0∞) * (R y w * (op R)^[n] 1 w) + R y w * (op R)^[n] VE w)
          ≤ ∑' w, R y w * (1 + VE w) := by
            refine ENNReal.tsum_le_tsum fun w => ?_
            by_cases hw : w ∈ C
            · simp [hRdef, hw]
            · have h1 := iter_one_le R hRrow n w
              have h2 := ih w hw
              calc ((n + 1 : ℕ) : ℝ≥0∞) * (R y w * (op R)^[n] 1 w) + R y w * (op R)^[n] VE w
                  = R y w * ((op R)^[n] 1 w
                      + ((n : ℝ≥0∞) * (op R)^[n] 1 w + (op R)^[n] VE w)) := by
                    push_cast; ring
                _ ≤ R y w * (1 + VE w) := mul_le_mul_right (add_le_add h1 h2) _
        _ = ∑' w, R y w + ∑' w, R y w * VE w := by
            rw [← ENNReal.tsum_add]; exact tsum_congr fun w => by ring
        _ ≤ 1 + ∑' w, Kk y w * VE w :=
            add_le_add (hRrow y) (ENNReal.tsum_le_tsum fun w => mul_le_mul_left (hRle y w) _)
        _ ≤ VE y := hfoster y hy
  have hFb : ∀ (n : ℕ) z, (n : ℝ≥0∞) * (op R)^[n + 1] 1 z ≤ ∑' w, Kk z w * VE w := by
    intro n z
    rw [Function.iterate_succ_apply']
    simp only [op]
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun w => ?_
    by_cases hw : w ∈ C
    · simp [hRdef, hw]
    · calc (n : ℝ≥0∞) * (R z w * (op R)^[n] 1 w) = R z w * ((n : ℝ≥0∞) * (op R)^[n] 1 w) := by
            ring
        _ ≤ Kk z w * VE w := mul_le_mul' (hRle z w) (le_self_add.trans (hF n w hw))
  -- the limit `h` of the taboo masses
  set g : ℕ → S → ℝ≥0∞ := fun n => (op P)^[n] 1 with hgdef
  have hg_anti : Antitone g := antitone_nat_of_succ_le fun n => by
    simp only [hgdef]
    rw [Function.iterate_succ_apply]
    exact (op_mono P).iterate n (op_one_le P hProw)
  set h : S → ℝ≥0∞ := fun z => ⨅ n, g n z with hhdef
  have hh1 : ∀ z, h z ≤ 1 := fun z => iInf_le_of_le 0 (by simp [hgdef])
  have hhsub : h ≤ op P h := by
    intro z
    calc h z ≤ ⨅ n, g (n + 1) z := le_iInf fun n => iInf_le _ (n + 1)
      _ = ⨅ n, ∑' w, P z w * g n w := by
          refine iInf_congr fun n => ?_
          simp only [hgdef]
          rw [Function.iterate_succ_apply']
          rfl
      _ ≤ ∑' w, P z w * ⨅ n, g n w :=
          iInf_tsum_le (P z) (fun w => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hPle z w))
            g hg_anti
            (by
              refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
              simpa [hgdef] using hProw z)
      _ = op P h z := rfl
  -- maximum principle off `C`
  have hmax : ∀ M : ℝ≥0∞, (∀ y ∈ C, h y ≤ M) → ∀ z, h z ≤ M := by
    intro M hM
    set u : S → ℝ≥0∞ := fun z => h z - M with hudef
    have huC : ∀ w ∈ C, u w = 0 := fun w hw => tsub_eq_zero_of_le (hM w hw)
    have hu : u ≤ op R u := by
      intro z
      by_cases hz : z ∈ C
      · rw [huC z hz]; exact zero_le
      · refine tsub_le_iff_right.mpr ?_
        calc h z ≤ op P h z := hhsub z
          _ ≤ ∑' w, Kk z w * h w := ENNReal.tsum_le_tsum fun w => mul_le_mul_left (hPle z w) _
          _ ≤ ∑' w, Kk z w * (u w + M) :=
              ENNReal.tsum_le_tsum fun w => mul_le_mul_right le_tsub_add _
          _ = ∑' w, Kk z w * u w + M * ∑' w, Kk z w := by
              rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
              exact tsum_congr fun w => by ring
          _ ≤ ∑' w, R z w * u w + M := by
              refine add_le_add (le_of_eq (tsum_congr fun w => ?_)) ?_
              · by_cases hw : w ∈ C
                · simp [huC w hw]
                · simp [hRdef, hw]
              · simpa using mul_le_mul_right (hKrow z) M
          _ = op R u z + M := rfl
    have hu1 : u ≤ 1 := fun z => tsub_le_self.trans (hh1 z)
    intro z
    have hle : ∀ n : ℕ, u z * n ≤ ∑' w, Kk z w * VE w := by
      intro n
      calc u z * n ≤ (op R)^[n + 1] 1 z * n :=
            mul_le_mul_left ((iter_ge R u hu (n + 1) z).trans
              ((op_mono R).iterate (n + 1) hu1 z)) _
        _ = (n : ℝ≥0∞) * (op R)^[n + 1] 1 z := mul_comm _ _
        _ ≤ _ := hFb n z
    have hu0 : u z = 0 := by
      by_contra hne
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hne (hfin z)
      exact absurd (hle n) (not_le.mpr (by rwa [mul_comm] at hn))
    exact tsub_eq_zero_iff_le.mp hu0
  have hzero : ∀ z, h z = 0 := by
    rcases C.eq_empty_or_nonempty with hCe | hCne
    · intro z
      exact le_antisymm (hmax 0 (by simp [hCe]) z) zero_le
    · obtain ⟨y, hyC, hymax⟩ := Set.exists_max_image C h hC hCne
      have hle : ∀ z, h z ≤ h y := hmax (h y) hymax
      obtain ⟨n, hn⟩ := hacc y hyC
      have hKrow' : ∀ a, ∑' b, ENNReal.ofReal (K a b) ≤ 1 := hKrow
      have hn' : KE Kk n y z₀ ≠ 0 := by
        intro h0
        rw [stepProb_eq' K hK.1 hKrow' n y z₀] at hn
        change 0 < (KE Kk n y z₀).toReal at hn
        rw [h0] at hn; simp at hn
      set δ := KE Kk (n + 1) y z₀ with hδ
      have hδ0 : δ ≠ 0 := by
        have : KE Kk n y z₀ * Kk z₀ z₀ ≤ δ := ENNReal.le_tsum (f := fun w => KE Kk n y w * Kk w z₀) z₀
        refine ne_of_gt (lt_of_lt_of_le ?_ this)
        exact ENNReal.mul_pos hn' (ENNReal.ofReal_pos.mpr hz₀).ne'
      have hmass : ∑' c, KE P (n + 1) y c + δ ≤ 1 := by
        have hP0 : KE P (n + 1) y z₀ = 0 := by
          simp [KE, hPdef]
        have e1 := ENNReal.tsum_eq_add_tsum_ite (f := fun c => KE P (n + 1) y c) z₀
        have e2 := ENNReal.tsum_eq_add_tsum_ite (f := fun c => KE Kk (n + 1) y c) z₀
        refine le_trans ?_ (KE_row_le Kk hKrow (n + 1) y)
        rw [e1, e2, hP0, zero_add]
        refine (add_le_add (ENNReal.tsum_le_tsum fun c => ?_) le_rfl).trans_eq (add_comm _ _)
        split_ifs
        · exact le_rfl
        · exact KE_mono P Kk hPle (n + 1) y c
      have hδ1 : δ ≤ 1 := le_trans le_add_self hmass
      have hstep : h y ≤ h y * (1 - δ) := by
        calc h y ≤ (op P)^[n + 1] h y := iter_ge P h hhsub (n + 1) y
          _ ≤ (op P)^[n + 1] (fun w => h y * (1 : S → ℝ≥0∞) w) y :=
              (op_mono P).iterate (n + 1) (fun w => by simpa using hle w) y
          _ = h y * (op P)^[n + 1] 1 y := by rw [iter_const_mul]
          _ = h y * ∑' c, KE P (n + 1) y c := by rw [KE_op1]
          _ ≤ h y * (1 - δ) := mul_le_mul_right (ENNReal.le_sub_of_add_le_right
              (ne_top_of_le_ne_top ENNReal.one_ne_top hδ1) hmass) _
      have hMtop : h y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hh1 y)
      have hsum : h y * (1 - δ) + h y * δ = h y := by
        rw [← mul_add, tsub_add_cancel_of_le hδ1, mul_one]
      have hMδ : h y * δ = 0 := by
        have h2 : h y + h y * δ ≤ h y + 0 := by
          calc h y + h y * δ ≤ h y * (1 - δ) + h y * δ := add_le_add hstep le_rfl
            _ = h y + 0 := by rw [hsum, add_zero]
        exact le_antisymm ((ENNReal.add_le_add_iff_left hMtop).mp h2) zero_le
      have hM0 : h y = 0 := by
        rcases mul_eq_zero.mp hMδ with h0 | h0
        · exact h0
        · exact absurd h0 hδ0
      intro z
      exact le_antisymm ((hle z).trans hM0.le) zero_le
  -- conclusion
  have hQ0 : ∀ a b, 0 ≤ (if b = z₀ then 0 else K a b) := fun a b => by
    split_ifs
    · exact le_rfl
    · exact hK.1 a b
  have hPQ : (fun a b => ENNReal.ofReal (if b = z₀ then 0 else K a b)) = P := by
    funext a b
    simp only [hPdef, hKk]
    split_ifs <;> simp
  have hQrow : ∀ a, ∑' b, ENNReal.ofReal (if b = z₀ then 0 else K a b) ≤ 1 := fun a => by
    have := hProw a
    rw [← hPQ] at this
    exact this
  have heq : ∀ n, ∑' y, stepProb (fun a b => if b = z₀ then 0 else K a b) n x y
      = (g n x).toReal := by
    intro n
    simp_rw [stepProb_eq' _ hQ0 hQrow n x, hPQ]
    rw [← ENNReal.tsum_toReal_eq (fun c => KE_ne_top P hProw n x c), KE_op1]
  simp_rw [heq]
  have hlim : Tendsto (fun n => g n x) atTop (𝓝 0) := by
    have := tendsto_atTop_iInf (fun m n (hmn : m ≤ n) => hg_anti hmn x)
    rwa [show (⨅ n, g n x) = 0 from hzero x] at this
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  simpa [Function.comp_def] using this

end SC9aK4H



set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped ENNReal
open StrictCompatLB.MeanField

namespace SC9aK4D

/-- D1: in Durrett's conventions, a positive `n+1`-step probability gives a positive hitting
probability (renewal decomposition, Durrett 5.3). Needs `Σ_m fᵐ(x,y) ≤ 1` (summability). -/
def D1Stmt : Prop :=
  ∀ {S : Type} [DecidableEq S] [Countable S] (p : S → S → ℝ),
    DurrettProbability.IsTransition p → ∀ (n : ℕ) (x y : S),
    0 < DurrettProbability.stepProb p (n + 1) x y → 0 < DurrettProbability.hitProb p x y

/-- D4: left and right Chapman-Kolmogorov recursions agree. -/
def D4Stmt : Prop :=
  ∀ {S : Type} [DecidableEq S] [Countable S] (K : S → S → ℝ), IsStochasticKernel K →
    ∀ (n : ℕ) (x y : S),
    StrictCompatLB.MeanField.stepProb K n x y = DurrettProbability.stepProb K n x y

/-- D5 (Scheffé): pointwise convergence of probability vectors gives `ℓ¹` convergence. -/
theorem scheffe {S : Type} [Countable S] (q : ℕ → S → ℝ) (π : S → ℝ)
    (hq : ∀ n, IsProbVec (q n)) (hπ : IsProbVec π)
    (hconv : ∀ y, Tendsto (fun n => q n y) atTop (𝓝 (π y))) :
    Tendsto (fun n => ∑' y, |q n y - π y|) atTop (𝓝 0) := by
  have hmaxs : ∀ n, Summable (fun y => max (π y - q n y) 0) := fun n =>
    Summable.of_nonneg_of_le (fun y => le_max_right _ _)
      (fun y => max_le (by linarith [(hq n).1 y]) (hπ.1 y)) hπ.2.summable
  have hid : ∀ n, ∑' y, |q n y - π y| = 2 * ∑' y, max (π y - q n y) 0 := by
    intro n
    have hpt : ∀ y, |q n y - π y| = (q n y - π y) + 2 * max (π y - q n y) 0 := by
      intro y
      rcases le_total (q n y) (π y) with h | h
      · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]; ring
      · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]; ring
    simp_rw [hpt]
    have hsub : HasSum (fun y => q n y - π y) 0 := by
      simpa using (hq n).2.sub hπ.2
    rw [(hsub.add ((hmaxs n).hasSum.mul_left 2)).tsum_eq, zero_add]
  simp_rw [hid]
  have ht : Tendsto (fun n => ∑' y, max (π y - q n y) 0) atTop (𝓝 (∑' _ : S, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := π) hπ.2.summable (fun y => ?_) ?_
    · have := ((tendsto_const_nhds (x := π y)).sub (hconv y)).max
        (tendsto_const_nhds (x := (0 : ℝ)))
      simpa using this
    · refine Eventually.of_forall fun n y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [(hq n).1 y]) (hπ.1 y)
  simpa using ht.const_mul 2

section CK
variable {S : Type*} [DecidableEq S]

/-- `n`-step kernel in `ℝ≥0∞` (right recursion, as `MeanField.stepProb`). -/
noncomputable def Kn (K : S → S → ℝ) : ℕ → S → S → ℝ≥0∞
  | 0 => fun a b => if b = a then 1 else 0
  | n + 1 => fun a b => ∑' y, Kn K n a y * ENNReal.ofReal (K y b)

lemma Kn_row (K : S → S → ℝ) (hK : IsStochasticKernel K) :
    ∀ n a, ∑' b, Kn K n a b = 1 := by
  intro n
  induction n with
  | zero =>
    intro a
    simp only [Kn]
    rw [tsum_eq_single a (fun b hb => by simp [hb])]
    simp
  | succ n ih =>
    intro a
    simp only [Kn]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    have hrow : ∀ y, ∑' b, ENNReal.ofReal (K y b) = 1 := fun y => by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun b => hK.1 y b) (hK.2 y).summable, (hK.2 y).tsum_eq,
        ENNReal.ofReal_one]
    simp_rw [hrow, mul_one, ih]

lemma Kn_ne_top (K : S → S → ℝ) (hK : IsStochasticKernel K) (n : ℕ) (a b : S) :
    Kn K n a b ≠ ⊤ := by
  have : Kn K n a b ≤ 1 := by rw [← Kn_row K hK n a]; exact ENNReal.le_tsum b
  exact (this.trans_lt ENNReal.one_lt_top).ne

lemma stepProb_eq (K : S → S → ℝ) (hK : IsStochasticKernel K) :
    ∀ n a b, stepProb K n a b = (Kn K n a b).toReal := by
  intro n
  induction n with
  | zero =>
    intro a b
    simp only [stepProb, Kn]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  | succ n ih =>
    intro a b
    simp only [stepProb, Kn]
    rw [ENNReal.tsum_toReal_eq (fun y => ENNReal.mul_ne_top (Kn_ne_top K hK n a y)
      ENNReal.ofReal_ne_top)]
    refine tsum_congr fun y => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hK.1 y b), ih]

/-- Left recursion of the `ℝ≥0∞` kernel. -/
lemma Kn_left (K : S → S → ℝ) :
    ∀ n a b, Kn K (n + 1) a b = ∑' y, ENNReal.ofReal (K a y) * Kn K n y b := by
  intro n
  induction n with
  | zero =>
    intro a b
    show ∑' y, (if y = a then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal (K y b) =
      ∑' y, ENNReal.ofReal (K a y) * (if b = y then (1 : ℝ≥0∞) else 0)
    rw [tsum_eq_single a (fun y hy => by simp [hy]), tsum_eq_single b (fun y hy => by simp [Ne.symm hy])]
    simp
  | succ n ih =>
    intro a b
    show ∑' y, Kn K (n + 1) a y * ENNReal.ofReal (K y b) = _
    conv_lhs => simp only [ih]
    simp_rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    rfl

lemma durrett_eq (K : S → S → ℝ) (hK : IsStochasticKernel K) :
    ∀ n a b, DurrettProbability.stepProb K n a b = (Kn K n a b).toReal := by
  intro n
  induction n with
  | zero =>
    intro a b
    simp only [DurrettProbability.stepProb, Kn]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  | succ n ih =>
    intro a b
    rw [Kn_left]
    simp only [DurrettProbability.stepProb]
    rw [ENNReal.tsum_toReal_eq (fun y => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (Kn_ne_top K hK n y b))]
    refine tsum_congr fun y => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hK.1 a y), ih]

end CK

theorem d4 : D4Stmt := by
  intro S _ _ K hK n x y
  rw [stepProb_eq K hK, durrett_eq K hK]

section FP
variable {S : Type*} [DecidableEq S]

/-- First-passage probabilities in `ℝ≥0∞`. -/
noncomputable def FE (p : S → S → ℝ) : ℕ → S → S → ℝ≥0∞
  | 0, _, _ => 0
  | 1, x, y => ENNReal.ofReal (p x y)
  | (n + 2), x, y => ∑' z, if z = y then 0 else ENNReal.ofReal (p x z) * FE p (n + 1) z y

lemma FE_partial (p : S → S → ℝ) (y : S) (hrow : ∀ x, ∑' z, ENNReal.ofReal (p x z) ≤ 1) :
    ∀ N x, ∑ n ∈ Finset.range N, FE p (n + 1) x y ≤ 1 := by
  intro N
  induction N with
  | zero => intro x; simp
  | succ N ih =>
    intro x
    rw [Finset.sum_range_succ']
    have h2 : ∀ n, FE p (n + 1 + 1) x y =
        ∑' z, if z = y then 0 else ENNReal.ofReal (p x z) * FE p (n + 1) z y := fun n => rfl
    have h1 : FE p (0 + 1) x y = ENNReal.ofReal (p x y) := rfl
    simp_rw [h2, h1]
    rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
    calc (∑' z, ∑ i ∈ Finset.range N,
            (if z = y then 0 else ENNReal.ofReal (p x z) * FE p (i + 1) z y)) + ENNReal.ofReal (p x y)
        ≤ (∑' z, if z = y then 0 else ENNReal.ofReal (p x z)) + ENNReal.ofReal (p x y) := by
          gcongr with z
          split_ifs
          · simp
          · rw [← Finset.mul_sum]
            exact (mul_le_mul' le_rfl (ih z)).trans (by simp)
      _ = ∑' z, ENNReal.ofReal (p x z) := by
          rw [ENNReal.tsum_eq_add_tsum_ite y (f := fun z => ENNReal.ofReal (p x z)), add_comm]
          congr 1
          exact tsum_congr fun z => by split_ifs <;> rfl
      _ ≤ 1 := hrow x

lemma FE_tsum_le (p : S → S → ℝ) (y : S) (hrow : ∀ x, ∑' z, ENNReal.ofReal (p x z) ≤ 1) (x : S) :
    ∑' n, FE p (n + 1) x y ≤ 1 :=
  ENNReal.tsum_le_of_sum_range_le fun N => FE_partial p y hrow N x

lemma FE_ne_top (p : S → S → ℝ) (y : S) (hrow : ∀ x, ∑' z, ENNReal.ofReal (p x z) ≤ 1)
    (n : ℕ) (x : S) : FE p n x y ≠ ⊤ := by
  cases n with
  | zero => exact ENNReal.zero_ne_top
  | succ n =>
    exact ((ENNReal.le_tsum n).trans (FE_tsum_le p y hrow x) |>.trans_lt ENNReal.one_lt_top).ne

lemma fp_eq (p : S → S → ℝ) (y : S) (h0 : ∀ a b, 0 ≤ p a b)
    (hrow : ∀ x, ∑' z, ENNReal.ofReal (p x z) ≤ 1) :
    ∀ n x, DurrettProbability.firstPassage p (n + 1) x y = (FE p (n + 1) x y).toReal := by
  intro n
  induction n with
  | zero =>
    intro x
    show p x y = (ENNReal.ofReal (p x y)).toReal
    rw [ENNReal.toReal_ofReal (h0 x y)]
  | succ n ih =>
    intro x
    show (∑' z, if z = y then 0 else p x z * DurrettProbability.firstPassage p (n + 1) z y) =
      (∑' z, if z = y then 0 else ENNReal.ofReal (p x z) * FE p (n + 1) z y).toReal
    rw [ENNReal.tsum_toReal_eq (fun z => by
      split_ifs
      · exact ENNReal.zero_ne_top
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (FE_ne_top p y hrow (n + 1) z))]
    refine tsum_congr fun z => ?_
    split_ifs
    · simp
    · rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (h0 x z), ih]

lemma dstep_nonneg (p : S → S → ℝ) (h0 : ∀ a b, 0 ≤ p a b) :
    ∀ n x y, 0 ≤ DurrettProbability.stepProb p n x y := by
  intro n
  induction n with
  | zero => intro x y; simp only [DurrettProbability.stepProb]; split_ifs <;> norm_num
  | succ n ih =>
    intro x y
    exact tsum_nonneg fun z => mul_nonneg (h0 x z) (ih z y)

lemma exists_pos_term {α : Type*} (f : α → ℝ) (hf : 0 < ∑' z, f z) : ∃ z, f z ≠ 0 := by
  by_contra h
  push Not at h
  simp [h] at hf

lemma FE_pos (p : S → S → ℝ) (y : S) (h0 : ∀ a b, 0 ≤ p a b) :
    ∀ n x, 0 < DurrettProbability.stepProb p (n + 1) x y → ∃ m, FE p (m + 1) x y ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro x hx
    obtain ⟨z, hz⟩ := exists_pos_term _ hx
    simp only [DurrettProbability.stepProb] at hz
    by_cases hzy : z = y
    · subst hzy
      refine ⟨0, ?_⟩
      show ENNReal.ofReal (p x z) ≠ 0
      have : p x z ≠ 0 := by simpa using hz
      exact (ENNReal.ofReal_pos.2 (lt_of_le_of_ne (h0 x z) (Ne.symm this))).ne'
    · simp [hzy] at hz
  | succ n ih =>
    intro x hx
    obtain ⟨z, hz⟩ := exists_pos_term _ hx
    have hpz : 0 < p x z := lt_of_le_of_ne (h0 x z) (fun h => hz (by rw [← h, zero_mul]))
    have hsz : 0 < DurrettProbability.stepProb p (n + 1) z y :=
      lt_of_le_of_ne (dstep_nonneg p h0 _ z y) (fun h => hz (by rw [← h, mul_zero]))
    by_cases hzy : z = y
    · subst hzy
      exact ⟨0, (ENNReal.ofReal_pos.2 hpz).ne'⟩
    · obtain ⟨m, hm⟩ := ih z hsz
      refine ⟨m + 1, ?_⟩
      show (∑' w, if w = y then 0 else ENNReal.ofReal (p x w) * FE p (m + 1) w y) ≠ 0
      intro h0'
      have hle := ENNReal.le_tsum (f := fun w =>
        if w = y then (0 : ℝ≥0∞) else ENNReal.ofReal (p x w) * FE p (m + 1) w y) z
      rw [h0'] at hle
      simp only [hzy, if_false, nonpos_iff_eq_zero, mul_eq_zero] at hle
      rcases hle with h | h
      · exact (ENNReal.ofReal_pos.2 hpz).ne' h
      · exact hm h

theorem d1 : D1Stmt := by
  intro S _ _ p hp n x y hpos
  have h0 := hp.1
  have hrow : ∀ x, ∑' z, ENNReal.ofReal (p x z) ≤ 1 := fun x => by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun b => h0 x b) (hp.2.1 x), hp.2.2 x, ENNReal.ofReal_one]
  obtain ⟨m, hm⟩ := FE_pos p y h0 n x hpos
  unfold DurrettProbability.hitProb
  simp_rw [fp_eq p y h0 hrow]
  rw [← ENNReal.tsum_toReal_eq (fun n => FE_ne_top p y hrow (n + 1) x)]
  refine ENNReal.toReal_pos ?_ ((FE_tsum_le p y hrow x).trans_lt ENNReal.one_lt_top).ne
  intro h
  exact hm (ENNReal.tsum_eq_zero.1 h m)

end FP

section D2
variable {S : Type} [DecidableEq S] [Countable S]

/-- `n`-step kernel of an `ℝ≥0∞` kernel (right recursion, like `stepProb`). -/
noncomputable def KE (P : S → S → ℝ≥0∞) : ℕ → S → S → ℝ≥0∞
  | 0 => fun a b => if a = b then 1 else 0
  | n + 1 => fun a b => ∑' y, KE P n a y * P y b

/-- The operator `f ↦ P f`. -/
noncomputable def op (P : S → S → ℝ≥0∞) (f : S → ℝ≥0∞) : S → ℝ≥0∞ :=
  fun x => ∑' w, P x w * f w

lemma op_mono (P : S → S → ℝ≥0∞) : Monotone (op P) := by
  intro f g hfg x
  exact ENNReal.tsum_le_tsum fun w => mul_le_mul_right (hfg w) _

lemma op_one_le (P : S → S → ℝ≥0∞) (hP : ∀ a, ∑' b, P a b ≤ 1) : op P 1 ≤ 1 := by
  intro x
  simpa [op] using hP x

lemma iter_one_le (P : S → S → ℝ≥0∞) (hP : ∀ a, ∑' b, P a b ≤ 1) :
    ∀ n, (op P)^[n] 1 ≤ 1 := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (op_mono P ih).trans (op_one_le P hP)

lemma iter_ge (P : S → S → ℝ≥0∞) (f : S → ℝ≥0∞) (hf : f ≤ op P f) :
    ∀ n, f ≤ (op P)^[n] f := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hf.trans (op_mono P ih)

lemma op_const_mul (P : S → S → ℝ≥0∞) (c : ℝ≥0∞) (f : S → ℝ≥0∞) :
    op P (fun w => c * f w) = fun x => c * op P f x := by
  funext x
  simp only [op]
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun w => by ring

lemma iter_const_mul (P : S → S → ℝ≥0∞) (c : ℝ≥0∞) (f : S → ℝ≥0∞) (n : ℕ) :
    (op P)^[n] (fun w => c * f w) = fun x => c * (op P)^[n] f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, op_const_mul]

lemma KE_op (P : S → S → ℝ≥0∞) :
    ∀ n (f : S → ℝ≥0∞) x, ∑' b, KE P n x b * f b = (op P)^[n] f x := by
  intro n
  induction n with
  | zero =>
    intro f x
    simp only [KE, Function.iterate_zero, id]
    rw [tsum_eq_single x (fun b hb => by simp [Ne.symm hb])]
    simp
  | succ n ih =>
    intro f x
    simp only [KE]
    simp_rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    rw [Function.iterate_succ_apply]
    exact ih (op P f) x

lemma KE_op1 (P : S → S → ℝ≥0∞) (n : ℕ) (x : S) :
    ∑' b, KE P n x b = (op P)^[n] 1 x := by
  simpa using KE_op P n 1 x

lemma KE_row_le (P : S → S → ℝ≥0∞) (hP : ∀ a, ∑' b, P a b ≤ 1) :
    ∀ n a, ∑' b, KE P n a b ≤ 1 := by
  intro n a
  rw [KE_op1]
  exact iter_one_le P hP n a

lemma KE_ne_top (P : S → S → ℝ≥0∞) (hP : ∀ a, ∑' b, P a b ≤ 1) (n : ℕ) (a b : S) :
    KE P n a b ≠ ⊤ :=
  ((ENNReal.le_tsum b).trans (KE_row_le P hP n a) |>.trans_lt ENNReal.one_lt_top).ne

lemma KE_mono (P P' : S → S → ℝ≥0∞) (h : ∀ a b, P a b ≤ P' a b) :
    ∀ n a b, KE P n a b ≤ KE P' n a b := by
  intro n
  induction n with
  | zero => intro a b; exact le_rfl
  | succ n ih =>
    intro a b
    exact ENNReal.tsum_le_tsum fun y => mul_le_mul' (ih a y) (h y b)

lemma stepProb_eq' (K : S → S → ℝ) (h0 : ∀ a b, 0 ≤ K a b)
    (hrow : ∀ a, ∑' b, ENNReal.ofReal (K a b) ≤ 1) :
    ∀ n a b, stepProb K n a b = (KE (fun a b => ENNReal.ofReal (K a b)) n a b).toReal := by
  intro n
  induction n with
  | zero =>
    intro a b
    simp only [stepProb, KE]
    split_ifs <;> simp
  | succ n ih =>
    intro a b
    simp only [stepProb, KE]
    rw [ENNReal.tsum_toReal_eq (fun y => ENNReal.mul_ne_top (KE_ne_top _ hrow n a y)
      ENNReal.ofReal_ne_top)]
    refine tsum_congr fun y => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (h0 y b), ih]

/-- Decreasing limits pass under a finite-mass sum. -/
lemma iInf_tsum_le (a : S → ℝ≥0∞) (ha : ∀ w, a w ≠ ⊤) (g : ℕ → S → ℝ≥0∞) (hg : Antitone g)
    (hfin : ∑' w, a w * g 0 w ≠ ⊤) :
    ⨅ n, ∑' w, a w * g n w ≤ ∑' w, a w * ⨅ n, g n w := by
  letI : MeasurableSpace S := ⊤
  haveI : MeasurableSingletonClass S := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have key := lintegral_iInf (μ := Measure.count) (f := fun n w => a w * g n w)
    (fun n => measurable_from_top) (fun m n hmn w => mul_le_mul_right (hg hmn w) _)
    (by rw [lintegral_count]; exact hfin)
  simp only [lintegral_count] at key
  rw [← key]
  refine ENNReal.tsum_le_tsum fun w => ?_
  by_cases ha0 : a w = 0
  · simp [ha0]
  · rw [ENNReal.mul_iInf_of_ne ha0 (ha w)]


lemma KE_left (P : S → S → ℝ≥0∞) :
    ∀ n a b, KE P (n + 1) a b = ∑' y, P a y * KE P n y b := by
  intro n
  induction n with
  | zero =>
    intro a b
    show ∑' y, (if a = y then (1 : ℝ≥0∞) else 0) * P y b =
      ∑' y, P a y * (if y = b then (1 : ℝ≥0∞) else 0)
    rw [tsum_eq_single a (fun y hy => by simp [Ne.symm hy]), tsum_eq_single b (fun y hy => by simp [hy])]
    simp
  | succ n ih =>
    intro a b
    show ∑' y, KE P (n + 1) a y * P y b = _
    conv_lhs => simp only [ih]
    simp_rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    rfl

/-- The taboo kernel (no entry into `z₀`). -/
def Qr (K : S → S → ℝ) (z₀ : S) : S → S → ℝ := fun a b => if b = z₀ then 0 else K a b

lemma taboo_eq_left (K : S → S → ℝ) (z₀ x : S)
    (hx : ∀ n, KE (fun a b => ENNReal.ofReal (K a b)) n z₀ x = 0) :
    ∀ n y, KE (fun a b => ENNReal.ofReal (K a b)) n y x =
      KE (fun a b => ENNReal.ofReal (Qr K z₀ a b)) n y x := by
  intro n
  induction n with
  | zero => intro y; rfl
  | succ n ih =>
    intro y
    rw [KE_left, KE_left]
    refine tsum_congr fun w => ?_
    by_cases hw : w = z₀
    · subst hw; rw [hx n]; simp [Qr]
    · rw [ih w]; simp [Qr, hw]

lemma taboo_eq_right (K : S → S → ℝ) (z₀ x : S)
    (hx : ∀ n, KE (fun a b => ENNReal.ofReal (K a b)) n x z₀ = 0) :
    ∀ n y, KE (fun a b => ENNReal.ofReal (K a b)) n x y =
      KE (fun a b => ENNReal.ofReal (Qr K z₀ a b)) n x y := by
  intro n
  induction n with
  | zero => intro y; rfl
  | succ n ih =>
    intro y
    by_cases hy : y = z₀
    · subst hy
      rw [hx (n + 1)]
      show (0 : ℝ≥0∞) = ∑' w, _ * ENNReal.ofReal (Qr K y w y)
      simp [Qr]
    · show ∑' w, _ * _ = ∑' w, _ * _
      refine tsum_congr fun w => ?_
      rw [ih w]; simp [Qr, hy]

lemma ofReal_stat (K : S → S → ℝ) (π : S → ℝ) (hπ : IsStationary K π) (hK : IsStochasticKernel K)
    (x : S) : ENNReal.ofReal (π x) = ∑' w, ENNReal.ofReal (π w) * ENNReal.ofReal (K w x) := by
  rw [← (hπ.2 x).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun w => mul_nonneg (hπ.1.1 w) (hK.1 w x))
    (hπ.2 x).summable]
  exact tsum_congr fun w => ENNReal.ofReal_mul (hπ.1.1 w)

lemma stat_iter (K : S → S → ℝ) (π : S → ℝ) (hπ : IsStationary K π) (hK : IsStochasticKernel K) :
    ∀ n x, ENNReal.ofReal (π x) =
      ∑' y, ENNReal.ofReal (π y) * KE (fun a b => ENNReal.ofReal (K a b)) n y x := by
  intro n
  induction n with
  | zero =>
    intro x
    show _ = ∑' y, ENNReal.ofReal (π y) * (if y = x then (1 : ℝ≥0∞) else 0)
    rw [tsum_eq_single x (fun y hy => by simp [hy])]
    simp
  | succ n ih =>
    intro x
    show _ = ∑' y, ENNReal.ofReal (π y) *
      ∑' w, KE (fun a b => ENNReal.ofReal (K a b)) n y w * ENNReal.ofReal (K w x)
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    simp_rw [← mul_assoc, ENNReal.tsum_mul_right, ← ih]
    exact ofReal_stat K π hπ hK x

lemma Q_row_le (K : S → S → ℝ) (hK : IsStochasticKernel K) (z₀ : S) (a : S) :
    ∑' b, ENNReal.ofReal (Qr K z₀ a b) ≤ 1 := by
  calc ∑' b, ENNReal.ofReal (Qr K z₀ a b) ≤ ∑' b, ENNReal.ofReal (K a b) :=
        ENNReal.tsum_le_tsum fun b => ENNReal.ofReal_le_ofReal (by
          simp only [Qr]; split_ifs
          · exact hK.1 a b
          · exact le_rfl)
    _ = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun b => hK.1 a b) (hK.2 a).summable, (hK.2 a).tsum_eq,
        ENNReal.ofReal_one]

lemma Qr_nonneg (K : S → S → ℝ) (hK : IsStochasticKernel K) (z₀ : S) (a b : S) :
    0 ≤ Qr K z₀ a b := by
  simp only [Qr]; split_ifs
  · exact le_rfl
  · exact hK.1 a b

/-- Real taboo mass → 0 gives `ℝ≥0∞` taboo mass → 0. -/
lemma g_tendsto (K : S → S → ℝ) (hK : IsStochasticKernel K) (z₀ y : S)
    (hH : Tendsto (fun n => ∑' x', stepProb (Qr K z₀) n y x') atTop (𝓝 0)) :
    Tendsto (fun n => ∑' x', KE (fun a b => ENNReal.ofReal (Qr K z₀ a b)) n y x') atTop (𝓝 0) := by
  have hne : ∀ n, ∑' x', KE (fun a b => ENNReal.ofReal (Qr K z₀ a b)) n y x' ≠ ⊤ := fun n =>
    ((KE_row_le _ (Q_row_le K hK z₀) n y).trans_lt ENNReal.one_lt_top).ne
  rw [← ENNReal.tendsto_toReal_iff hne ENNReal.zero_ne_top]
  simp only [ENNReal.toReal_zero]
  refine hH.congr fun n => ?_
  rw [ENNReal.tsum_toReal_eq (fun x' => KE_ne_top _ (Q_row_le K hK z₀) n y x')]
  exact tsum_congr fun x' => stepProb_eq' (Qr K z₀) (Qr_nonneg K hK z₀) (Q_row_le K hK z₀) n y x'

/-- D2: the stationary law vanishes off the closed class of `z₀`. -/
theorem pi_zero_off (K : S → S → ℝ) (hK : IsStochasticKernel K) (π : S → ℝ) (hπ : IsStationary K π)
    (z₀ : S) (hH : ∀ y, Tendsto (fun n => ∑' x', stepProb (Qr K z₀) n y x') atTop (𝓝 0))
    (x : S) (hx : ∀ n, KE (fun a b => ENNReal.ofReal (K a b)) n z₀ x = 0) : π x = 0 := by
  set Qe : S → S → ℝ≥0∞ := fun a b => ENNReal.ofReal (Qr K z₀ a b) with hQe
  set g : ℕ → S → ℝ≥0∞ := fun n y => ∑' x', KE Qe n y x' with hg
  have h1 : ∀ n, ENNReal.ofReal (π x) ≤ ∑' y, ENNReal.ofReal (π y) * g n y := by
    intro n
    rw [stat_iter K π hπ hK n x]
    refine ENNReal.tsum_le_tsum fun y => mul_le_mul' le_rfl ?_
    rw [taboo_eq_left K z₀ x hx n y]
    exact ENNReal.le_tsum x
  have hanti : Antitone g := by
    refine antitone_nat_of_succ_le fun n y => ?_
    simp only [hg, KE_op1]
    rw [Function.iterate_succ_apply]
    exact Monotone.iterate (op_mono Qe) n (op_one_le Qe (Q_row_le K hK z₀)) y
  have hfin : ∑' y, ENNReal.ofReal (π y) * g 0 y ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' y, ENNReal.ofReal (π y)) ?_ ?_
    · rw [← ENNReal.ofReal_tsum_of_nonneg hπ.1.1 hπ.1.2.summable, hπ.1.2.tsum_eq]
      exact ENNReal.ofReal_ne_top
    · exact ENNReal.tsum_le_tsum fun y => mul_le_of_le_one_right zero_le (KE_row_le _ (Q_row_le K hK z₀) 0 y)
  have hinf : ∀ y, ⨅ n, g n y = 0 := fun y =>
    le_antisymm (ge_of_tendsto' (g_tendsto K hK z₀ y (hH y)) (fun n => iInf_le (fun n => g n y) n)) zero_le
  have h2 := iInf_tsum_le (fun y => ENNReal.ofReal (π y)) (fun _ => ENNReal.ofReal_ne_top) g hanti hfin
  simp only [hinf, mul_zero, tsum_zero, nonpos_iff_eq_zero] at h2
  have h3 : ENNReal.ofReal (π x) ≤ 0 := by
    rw [← h2]; exact le_iInf h1
  have := ENNReal.ofReal_eq_zero.1 (le_antisymm h3 zero_le)
  exact le_antisymm this (hπ.1.1 x)

lemma Ke_row (K : S → S → ℝ) (hK : IsStochasticKernel K) (a : S) :
    ∑' b, ENNReal.ofReal (K a b) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun b => hK.1 a b) (hK.2 a).summable, (hK.2 a).tsum_eq,
    ENNReal.ofReal_one]

lemma KE_row_eq (K : S → S → ℝ) (hK : IsStochasticKernel K) (n : ℕ) (x : S) :
    ∑' b, KE (fun a b => ENNReal.ofReal (K a b)) n x b = 1 := by
  rw [KE_op1]
  have hfix : op (fun a b => ENNReal.ofReal (K a b)) 1 = 1 := by
    funext a; simp [op, Ke_row K hK a]
  rw [Function.iterate_fixed hfix]
  rfl

/-- D2b: under the taboo hypothesis every state reaches `z₀`. -/
theorem reach_z0 (K : S → S → ℝ) (hK : IsStochasticKernel K) (z₀ : S)
    (hH : ∀ y, Tendsto (fun n => ∑' x', stepProb (Qr K z₀) n y x') atTop (𝓝 0)) (x : S) :
    ∃ m, KE (fun a b => ENNReal.ofReal (K a b)) m x z₀ ≠ 0 := by
  by_contra h
  push Not at h
  have heq := taboo_eq_right K z₀ x h
  have hone : ∀ n, ∑' x', KE (fun a b => ENNReal.ofReal (Qr K z₀ a b)) n x x' = 1 := fun n => by
    simp_rw [← heq n]; exact KE_row_eq K hK n x
  have ht := g_tendsto K hK z₀ x (hH x)
  simp_rw [hone] at ht
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)

end D2

section D3
variable {S : Type} [DecidableEq S] [Countable S]

lemma KE_add (P : S → S → ℝ≥0∞) (a : ℕ) :
    ∀ b x y, KE P (a + b) x y = ∑' w, KE P a x w * KE P b w y := by
  intro b
  induction b with
  | zero =>
    intro x y
    rw [Nat.add_zero, tsum_eq_single y (fun w hw => by simp [KE, hw])]
    simp [KE]
  | succ b ih =>
    intro x y
    rw [← Nat.add_assoc]
    simp only [KE]
    calc ∑' u, KE P (a + b) x u * P u y = ∑' u, ∑' w, KE P a x w * KE P b w u * P u y := by
          refine tsum_congr fun u => ?_
          rw [ih, ← ENNReal.tsum_mul_right]
      _ = ∑' w, ∑' u, KE P a x w * KE P b w u * P u y := ENNReal.tsum_comm
      _ = ∑' w, KE P a x w * ∑' u, KE P b w u * P u y := by
          refine tsum_congr fun w => ?_
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun u => ?_
          ring

lemma KE_lb (P : S → S → ℝ≥0∞) (a b : ℕ) (x w y : S) :
    KE P a x w * KE P b w y ≤ KE P (a + b) x y := by
  rw [KE_add]; exact ENNReal.le_tsum w

/-- The closed class of `z₀`: states reachable from `z₀`. -/
def RS (K : S → S → ℝ) (z₀ : S) : Set S :=
  {x | ∃ n, KE (fun a b => ENNReal.ofReal (K a b)) n z₀ x ≠ 0}

lemma RS_closed (K : S → S → ℝ) (hK : IsStochasticKernel K) (z₀ : S) :
    ∀ x ∈ RS K z₀, ∀ z, K x z ≠ 0 → z ∈ RS K z₀ := by
  intro x hx z hz
  obtain ⟨n, hn⟩ := hx
  refine ⟨n + 1, ?_⟩
  have h1 : ENNReal.ofReal (K x z) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (lt_of_le_of_ne (hK.1 x z) (Ne.symm hz))).ne'
  have hle : KE (fun a b => ENNReal.ofReal (K a b)) n z₀ x * ENNReal.ofReal (K x z) ≤
      KE (fun a b => ENNReal.ofReal (K a b)) (n + 1) z₀ z := by
    simp only [KE]
    exact ENNReal.le_tsum x
  exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 (mul_ne_zero hn h1)) hle)

lemma dpos_iff (K : S → S → ℝ) (hK : IsStochasticKernel K) (n : ℕ) (x y : S) :
    0 < DurrettProbability.stepProb K n x y ↔
      KE (fun a b => ENNReal.ofReal (K a b)) n x y ≠ 0 := by
  have hrow : ∀ a, ∑' b, ENNReal.ofReal (K a b) ≤ 1 := fun a => (Ke_row K hK a).le
  rw [← d4 K hK n x y, stepProb_eq' K hK.1 hrow n x y, ENNReal.toReal_pos_iff]
  have := KE_ne_top _ hrow n x y
  constructor
  · intro h; exact h.1.ne'
  · intro h; exact ⟨pos_iff_ne_zero.2 h, lt_top_iff_ne_top.2 this⟩

/-- The restriction of `K` to a set. -/
def pR (K : S → S → ℝ) (R : Set S) : R → R → ℝ := fun x y => K x y

lemma dsub (K : S → S → ℝ) (R : Set S) (hcl : ∀ x ∈ R, ∀ z, K x z ≠ 0 → z ∈ R) :
    ∀ n (x y : R), DurrettProbability.stepProb (pR K R) n x y =
      DurrettProbability.stepProb K n x y := by
  intro n
  induction n with
  | zero =>
    intro x y
    rcases eq_or_ne x y with h | h
    · subst h; simp [DurrettProbability.stepProb]
    · simp [DurrettProbability.stepProb, h, Subtype.coe_ne_coe.2 h]
  | succ n ih =>
    intro x y
    simp only [DurrettProbability.stepProb, pR, ih]
    exact tsum_subtype_eq_of_support_subset
      (f := fun z => K x z * DurrettProbability.stepProb K n z y)
      (fun z hz => hcl x x.2 z (left_ne_zero_of_mul hz))

lemma trans_sub (K : S → S → ℝ) (hK : IsStochasticKernel K) (R : Set S)
    (hcl : ∀ x ∈ R, ∀ z, K x z ≠ 0 → z ∈ R) : DurrettProbability.IsTransition (pR K R) := by
  refine ⟨fun x y => hK.1 x y, fun x => (hK.2 x).summable.subtype R, fun x => ?_⟩
  show ∑' y : R, K x y = 1
  rw [tsum_subtype_eq_of_support_subset (f := K x) (fun z hz => hcl x x.2 z hz), (hK.2 x).tsum_eq]

/-- Durrett's convergence theorem, as a hypothesis (it is the Proved theorem 3dd9a79f). -/
def DStmt : Prop :=
  ∀ {T : Type} [Countable T] [DecidableEq T] (p : T → T → ℝ),
    DurrettProbability.IsTransition p → DurrettProbability.Irreducible p →
    (∀ x, DurrettProbability.Aperiodic p x) → ∀ (π : T → ℝ), DurrettProbability.StationaryDist p π →
    ∀ x y, Tendsto (fun n : ℕ => DurrettProbability.stepProb p n x y) atTop (𝓝 (π y))

theorem conv_on_R (K : S → S → ℝ) (hK : IsStochasticKernel K) (z₀ : S) (hz₀ : 0 < K z₀ z₀)
    (hH : ∀ y, Tendsto (fun n => ∑' x', stepProb (Qr K z₀) n y x') atTop (𝓝 0))
    (π : S → ℝ) (hπ : IsStationary K π) (hD : DStmt) (x : S) (hx : x ∈ RS K z₀) (y : S) :
    Tendsto (fun n => stepProb K n x y) atTop (𝓝 (π y)) := by
  have hrow : ∀ a, ∑' b, ENNReal.ofReal (K a b) ≤ 1 := fun a => (Ke_row K hK a).le
  have hcl := RS_closed K hK z₀
  have hKz : ENNReal.ofReal (K z₀ z₀) ≠ 0 := (ENNReal.ofReal_pos.2 hz₀).ne'
  have hchain : ∀ (u v : S) (m k : ℕ), KE (fun a b => ENNReal.ofReal (K a b)) m u z₀ ≠ 0 →
      KE (fun a b => ENNReal.ofReal (K a b)) k z₀ v ≠ 0 →
      ∀ j, KE (fun a b => ENNReal.ofReal (K a b)) (m + j + k) u v ≠ 0 := by
    intro u v m k hm hk j
    have hj : KE (fun a b => ENNReal.ofReal (K a b)) (m + j) u z₀ ≠ 0 := by
      induction j with
      | zero => simpa using hm
      | succ j ihj =>
        have hle : KE (fun a b => ENNReal.ofReal (K a b)) (m + j) u z₀ * ENNReal.ofReal (K z₀ z₀) ≤
            KE (fun a b => ENNReal.ofReal (K a b)) (m + j + 1) u z₀ := by
          simp only [KE]
          exact ENNReal.le_tsum z₀
        rw [← Nat.add_assoc]
        exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 (mul_ne_zero ihj hKz)) hle)
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 (mul_ne_zero hj hk)) (KE_lb _ (m + j) k u z₀ v))
  have hdsub := dsub K (RS K z₀) hcl
  have hT := trans_sub K hK (RS K z₀) hcl
  have hirr : DurrettProbability.Irreducible (pR K (RS K z₀)) := by
    intro u v
    obtain ⟨m, hm⟩ := reach_z0 K hK z₀ hH u
    obtain ⟨k, hk⟩ := v.2
    refine d1 (pR K (RS K z₀)) hT (m + k) u v ?_
    rw [hdsub, dpos_iff K hK]
    have e : m + k + 1 = m + 1 + k := by omega
    rw [e]; exact hchain u v m k hm hk 1
  have haper : ∀ u, DurrettProbability.Aperiodic (pR K (RS K z₀)) u := by
    intro u d hd
    obtain ⟨m, hm⟩ := reach_z0 K hK z₀ hH u
    obtain ⟨k, hk⟩ := u.2
    have h1 := hd (m + 1 + k) (by omega) (by rw [hdsub, dpos_iff K hK]; exact hchain u u m k hm hk 1)
    have h2 := hd (m + 2 + k) (by omega) (by rw [hdsub, dpos_iff K hK]; exact hchain u u m k hm hk 2)
    have e : m + 2 + k = (m + 1 + k) + 1 := by omega
    rw [e] at h2
    exact Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 h2)
  have hπ0 : ∀ u, u ∉ RS K z₀ → π u = 0 := fun u hu =>
    pi_zero_off K hK π hπ z₀ hH u (fun n => by by_contra h; exact hu ⟨n, h⟩)
  have hsupp : Function.support π ⊆ RS K z₀ := fun u hu => by
    by_contra h; exact hu (hπ0 u h)
  have hstat : DurrettProbability.StationaryDist (pR K (RS K z₀)) (fun u => π u) := by
    refine ⟨fun u => hπ.1.1 u, ?_, fun v => ?_⟩
    · show ∑' u : RS K z₀, π u = 1
      rw [tsum_subtype_eq_of_support_subset hsupp, hπ.1.2.tsum_eq]
    · show ∑' u : RS K z₀, π u * K u v = π v
      rw [tsum_subtype_eq_of_support_subset (f := fun u => π u * K u v)
        (fun u hu => hsupp (left_ne_zero_of_mul hu)), (hπ.2 v).tsum_eq]
  have hconvR := hD (pR K (RS K z₀)) hT hirr haper _ hstat ⟨x, hx⟩
  by_cases hy : y ∈ RS K z₀
  · have := hconvR ⟨y, hy⟩
    simp only [hdsub] at this
    simp_rw [d4 K hK]
    exact this
  · rw [hπ0 y hy]
    have h0 : ∀ n, stepProb K n x y = 0 := by
      intro n
      rw [stepProb_eq' K hK.1 hrow n x y]
      have : KE (fun a b => ENNReal.ofReal (K a b)) n x y = 0 := by
        by_contra h
        obtain ⟨k, hk⟩ := hx
        exact hy ⟨k + n, ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 (mul_ne_zero hk h))
          (KE_lb _ k n z₀ x y))⟩
      rw [this, ENNReal.toReal_zero]
    simp only [h0]
    exact tendsto_const_nhds

lemma row_prob (K : S → S → ℝ) (hK : IsStochasticKernel K) (n : ℕ) (x : S) :
    IsProbVec (fun y => stepProb K n x y) := by
  have hrow : ∀ a, ∑' b, ENNReal.ofReal (K a b) ≤ 1 := fun a => (Ke_row K hK a).le
  refine ⟨fun y => ?_, ?_⟩
  · show 0 ≤ stepProb K n x y
    rw [stepProb_eq' K hK.1 hrow]; exact ENNReal.toReal_nonneg
  · have hne : ∀ y, KE (fun a b => ENNReal.ofReal (K a b)) n x y ≠ ⊤ :=
      fun y => KE_ne_top _ hrow n x y
    have hs : ∑' y, KE (fun a b => ENNReal.ofReal (K a b)) n x y = 1 := KE_row_eq K hK n x
    simp_rw [stepProb_eq' K hK.1 hrow n x]
    have := (ENNReal.summable_toReal (by rw [hs]; exact ENNReal.one_ne_top)).hasSum
    rwa [← ENNReal.tsum_toReal_eq hne, hs, ENNReal.toReal_one] at this

theorem l1_on_R (K : S → S → ℝ) (hK : IsStochasticKernel K) (z₀ : S) (hz₀ : 0 < K z₀ z₀)
    (hH : ∀ y, Tendsto (fun n => ∑' x', stepProb (Qr K z₀) n y x') atTop (𝓝 0))
    (π : S → ℝ) (hπ : IsStationary K π) (hD : DStmt) (x : S) (hx : x ∈ RS K z₀) :
    Tendsto (fun n => ∑' y, |stepProb K n x y - π y|) atTop (𝓝 0) :=
  scheffe (fun n y => stepProb K n x y) π (fun n => row_prob K hK n x) hπ.1
    (conv_on_R K hK z₀ hz₀ hH π hπ hD x hx)

end D3

section D5
variable {S : Type} [DecidableEq S] [Countable S]

lemma ck_real (K : S → S → ℝ) (hK : IsStochasticKernel K) (j m : ℕ) (x y : S) :
    stepProb K (j + m) x y = ∑' w, stepProb K j x w * stepProb K m w y := by
  have hrow : ∀ a, ∑' b, ENNReal.ofReal (K a b) ≤ 1 := fun a => (Ke_row K hK a).le
  simp_rw [stepProb_eq' K hK.1 hrow]
  rw [KE_add, ENNReal.tsum_toReal_eq (fun w => ENNReal.mul_ne_top (KE_ne_top _ hrow j x w)
    (KE_ne_top _ hrow m w y))]
  simp_rw [ENNReal.toReal_mul]

lemma taboo_real (K : S → S → ℝ) (hK : IsStochasticKernel K) (z₀ x w : S) (hw : w ∉ RS K z₀)
    (j : ℕ) : stepProb K j x w = stepProb (Qr K z₀) j x w := by
  have hrow : ∀ a, ∑' b, ENNReal.ofReal (K a b) ≤ 1 := fun a => (Ke_row K hK a).le
  have hw' : ∀ n, KE (fun a b => ENNReal.ofReal (K a b)) n z₀ w = 0 := fun n => by
    by_contra h; exact hw ⟨n, h⟩
  rw [stepProb_eq' K hK.1 hrow, stepProb_eq' (Qr K z₀) (Qr_nonneg K hK z₀) (Q_row_le K hK z₀),
    taboo_eq_left K z₀ w hw' j x]

theorem conv_all (K : S → S → ℝ) (hK : IsStochasticKernel K) (z₀ : S) (hz₀ : 0 < K z₀ z₀)
    (hH : ∀ y, Tendsto (fun n => ∑' x', stepProb (Qr K z₀) n y x') atTop (𝓝 0))
    (π : S → ℝ) (hπ : IsStationary K π) (hD : DStmt) (x y : S) :
    Tendsto (fun n => stepProb K n x y) atTop (𝓝 (π y)) := by
  have hR : ∀ w ∈ RS K z₀, Tendsto (fun m => stepProb K m w y - π y) atTop (𝓝 0) := fun w hw => by
    have := (conv_on_R K hK z₀ hz₀ hH π hπ hD w hw y).sub_const (π y)
    simpa using this
  have hQ0 : ∀ j w, 0 ≤ stepProb (Qr K z₀) j x w := fun j w => by
    rw [stepProb_eq' (Qr K z₀) (Qr_nonneg K hK z₀) (Q_row_le K hK z₀)]; exact ENNReal.toReal_nonneg
  have hQs : ∀ j, Summable (fun w => stepProb (Qr K z₀) j x w) := fun j => by
    simp_rw [stepProb_eq' (Qr K z₀) (Qr_nonneg K hK z₀) (Q_row_le K hK z₀)]
    exact ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      (KE_row_le _ (Q_row_le K hK z₀) j x))
  have hP0 : ∀ n a b, 0 ≤ stepProb K n a b := fun n a b => (row_prob K hK n a).1 b
  have hrows : ∀ j, Summable (fun w => stepProb K j x w) := fun j => (row_prob K hK j x).2.summable
  have hb : ∀ n w, stepProb K n w y ≤ 1 := fun n w =>
    le_hasSum (row_prob K hK n w).2 y (fun b _ => hP0 n w b)
  have hπb : π y ≤ 1 := le_hasSum hπ.1.2 y (fun b _ => hπ.1.1 b)
  have hdiff : ∀ m w, |stepProb K m w y - π y| ≤ 1 := fun m w =>
    abs_sub_le_iff.2 ⟨by linarith [hb m w, hπ.1.1 y], by linarith [hP0 m w y, hπb]⟩
  have hFb : ∀ j m w, ‖stepProb K j x w * (stepProb K m w y - π y)‖ ≤ stepProb K j x w :=
    fun j m w => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hP0 j x w)]
      exact mul_le_of_le_one_right (hP0 j x w) (hdiff m w)
  have hFs : ∀ j m, Summable (fun w => stepProb K j x w * (stepProb K m w y - π y)) :=
    fun j m => Summable.of_norm_bounded (hrows j) (hFb j m)
  have hsumF : ∀ j m, ∑' w, stepProb K j x w * (stepProb K m w y - π y) =
      stepProb K (j + m) x y - π y := by
    intro j m
    have hs1 : Summable (fun w => stepProb K j x w * stepProb K m w y) :=
      Summable.of_nonneg_of_le (fun w => mul_nonneg (hP0 j x w) (hP0 m w y))
        (fun w => mul_le_of_le_one_right (hP0 j x w) (hb m w)) (hrows j)
    simp only [mul_sub]
    rw [Summable.tsum_sub hs1 ((hrows j).mul_right (π y)), ← ck_real K hK, tsum_mul_right,
      (row_prob K hK j x).2.tsum_eq, one_mul]
  set F : ℕ → ℕ → S → ℝ := fun j m w => stepProb K j x w * (stepProb K m w y - π y) with hF
  have hIb : ∀ (s : Set S) j m w, ‖s.indicator (F j m) w‖ ≤ stepProb K j x w := by
    intro s j m w
    by_cases hw : w ∈ s
    · rw [Set.indicator_of_mem hw]; exact hFb j m w
    · rw [Set.indicator_of_notMem hw, norm_zero]; exact hP0 j x w
  have hsplit : ∀ j m, ∑' w, F j m w =
      ∑' w, (RS K z₀).indicator (F j m) w + ∑' w, (RS K z₀)ᶜ.indicator (F j m) w := by
    intro j m
    rw [← Summable.tsum_add (Summable.of_norm_bounded (hrows j) (hIb _ j m))
      (Summable.of_norm_bounded (hrows j) (hIb _ j m))]
    exact tsum_congr fun w => (congrFun (Set.indicator_self_add_compl (RS K z₀) (F j m)) w).symm
  have hCb : ∀ j m w, ‖(RS K z₀)ᶜ.indicator (F j m) w‖ ≤ stepProb (Qr K z₀) j x w := by
    intro j m w
    by_cases hw : w ∈ RS K z₀
    · rw [Set.indicator_of_notMem (by simpa using hw), norm_zero]; exact hQ0 j w
    · rw [Set.indicator_of_mem hw, ← taboo_real K hK z₀ x w hw j]; exact hFb j m w
  have hcompl : ∀ j m, |∑' w, (RS K z₀)ᶜ.indicator (F j m) w| ≤
      ∑' w, stepProb (Qr K z₀) j x w := by
    intro j m
    have hn : Summable (fun w => ‖(RS K z₀)ᶜ.indicator (F j m) w‖) :=
      Summable.of_norm_bounded (hQs j) (fun w => by rw [norm_norm]; exact hCb j m w)
    rw [← Real.norm_eq_abs]
    exact (norm_tsum_le_tsum_norm hn).trans (hasSum_le (hCb j m) hn.hasSum (hQs j).hasSum)
  have hRj : ∀ j, Tendsto (fun m => ∑' w, (RS K z₀).indicator (F j m) w) atTop (𝓝 0) := by
    intro j
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := fun m w => (RS K z₀).indicator (F j m) w)
      (g := fun _ => (0 : ℝ)) (hrows j) (fun w => ?_) (Filter.Eventually.of_forall (hIb _ j))
    · simpa using this
    · by_cases hw : w ∈ RS K z₀
      · simp only [Set.indicator_of_mem hw, hF]
        simpa using (hR w hw).const_mul (stepProb K j x w)
      · simp only [Set.indicator_of_notMem hw]
        exact tendsto_const_nhds
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨j, hj⟩ : ∃ j, ∑' w, stepProb (Qr K z₀) j x w < ε / 2 :=
    ((hH x).eventually (gt_mem_nhds (half_pos hε))).exists
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 (hRj j) (ε / 2) (half_pos hε)
  refine ⟨j + M, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = j + m := ⟨n - j, by omega⟩
  have h1 := hM m (by omega)
  rw [Real.dist_eq, sub_zero] at h1
  rw [Real.dist_eq, ← hsumF j m]
  have h3 := hsplit j m
  simp only [hF] at h3
  rw [h3]
  have h2 := hcompl j m
  rw [abs_lt] at h1 ⊢
  rw [abs_le] at h2
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem l1_all (K : S → S → ℝ) (hK : IsStochasticKernel K) (z₀ : S) (hz₀ : 0 < K z₀ z₀)
    (hH : ∀ y, Tendsto (fun n => ∑' x', stepProb (Qr K z₀) n y x') atTop (𝓝 0))
    (π : S → ℝ) (hπ : IsStationary K π) (hD : DStmt) (x : S) :
    Tendsto (fun n => ∑' y, |stepProb K n x y - π y|) atTop (𝓝 0) :=
  scheffe (fun n y => stepProb K n x y) π (fun n => row_prob K hK n x) hπ.1
    (conv_all K hK z₀ hz₀ hH π hπ hD x)

end D5

section D6
variable {S : Type} [DecidableEq S] [Countable S]

lemma stat_real (K : S → S → ℝ) (hK : IsStochasticKernel K) (π' : S → ℝ) (hπ' : IsStationary K π')
    (n : ℕ) (y : S) : ∑' x, π' x * stepProb K n x y = π' y := by
  have hrow : ∀ a, ∑' b, ENNReal.ofReal (K a b) ≤ 1 := fun a => (Ke_row K hK a).le
  have h := congrArg ENNReal.toReal (stat_iter K π' hπ' hK n y)
  rw [ENNReal.toReal_ofReal (hπ'.1.1 y), ENNReal.tsum_toReal_eq (fun x =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (KE_ne_top _ hrow n x y))] at h
  rw [h]
  refine tsum_congr fun x => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hπ'.1.1 x), stepProb_eq' K hK.1 hrow]

theorem unique_stat (K : S → S → ℝ) (hK : IsStochasticKernel K) (z₀ : S) (hz₀ : 0 < K z₀ z₀)
    (hH : ∀ y, Tendsto (fun n => ∑' x', stepProb (Qr K z₀) n y x') atTop (𝓝 0))
    (π : S → ℝ) (hπ : IsStationary K π) (hD : DStmt) (π' : S → ℝ) (hπ' : IsStationary K π') :
    π' = π := by
  funext y
  have hlim : Tendsto (fun n => ∑' x, π' x * stepProb K n x y) atTop (𝓝 (∑' x, π' x * π y)) := by
    refine tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (bound := π') hπ'.1.2.summable
      (fun x => (conv_all K hK z₀ hz₀ hH π hπ hD x y).const_mul (π' x))
      (Filter.Eventually.of_forall fun n x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ'.1.1 x),
      abs_of_nonneg ((row_prob K hK n x).1 y)]
    exact mul_le_of_le_one_right (hπ'.1.1 x)
      (le_hasSum (row_prob K hK n x).2 y (fun b _ => (row_prob K hK n x).1 b))
  simp_rw [stat_real K hK π' hπ'] at hlim
  rw [tsum_mul_right, hπ'.1.2.tsum_eq, one_mul] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

end D6

end SC9aK4D




open MeasureTheory Filter Topology
open StrictCompatLB.MeanField

namespace SC9aK4

/-- K4 (generic ergodic theorem, Foster drift + aperiodic accessible atom; Meyn-Tweedie
Thm 11.3.4 + Thm 13.0.1, Norris Thm 1.8.3, Poissonised). -/
def K4Stmt : Prop :=
  ∀ {S : Type} [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    (K : S → S → ℝ), IsStochasticKernel K →
    ∀ (V : S → ℝ), (∀ z, 0 ≤ V z) → (∀ z, Summable (fun z' => K z z' * V z')) →
    ∀ (C : Set S), C.Finite → ∀ b : ℝ,
    (∀ z, oneStepDrift K V z ≤ -1 + b * C.indicator (fun _ => (1 : ℝ)) z) →
    ∀ z₀ : S, 0 < K z₀ z₀ → (∀ z ∈ C, ∃ n, 0 < stepProb K n z z₀) →
    ∀ π : S → ℝ, IsStationary K π →
    ∀ rate : ℝ, 0 < rate →
      (∀ π' : S → ℝ, IsStationary K π' → π' = π) ∧
      StrictCompatLB.FullInhomogeneous.AttractsAllStates K rate π


end SC9aK4


open StrictCompatLB.MeanField in
/-- K4 from Durrett's convergence theorem: K4H (taboo mass -> 0) + K4D (l1 ergodicity, uniqueness)
+ K4P (Poissonisation). -/
theorem SC9aK4.k4_of_durrett (hD : SC9aK4D.DStmt) : SC9aK4.K4Stmt := by
  intro S _ _ _ _ K hK V hV0 hVs C hC b hdrift z₀ hz₀ hacc π hπ rate hrate
  have hH : ∀ x, Tendsto (fun n => ∑' y, stepProb (SC9aK4D.Qr K z₀) n x y) atTop (𝓝 0) :=
    SC9aK4H.k4h K hK V hV0 hVs C hC b hdrift z₀ hz₀ hacc
  exact ⟨fun π' hπ' => SC9aK4D.unique_stat K hK z₀ hz₀ hH π hπ hD π' hπ',
    SC9aK4P.k4p K hK π hπ.1 rate (fun z => SC9aK4D.l1_all K hK z₀ hz₀ hH π hπ hD z)⟩

open MeasureTheory Filter Topology StrictCompatLB.MeanField StrictCompatLB.FullInhomogeneous in
theorem solution :
    ∀ {S : Type} [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
      (K : S → S → ℝ), IsStochasticKernel K →
      ∀ (V : S → ℝ), (∀ z, 0 ≤ V z) → (∀ z, Summable (fun z' => K z z' * V z')) →
      ∀ (C : Set S), C.Finite → ∀ b : ℝ,
      (∀ z, oneStepDrift K V z ≤ -1 + b * C.indicator (fun _ => (1 : ℝ)) z) →
      ∀ z₀ : S, 0 < K z₀ z₀ → (∀ z ∈ C, ∃ n, 0 < stepProb K n z z₀) →
      ∀ π : S → ℝ, IsStationary K π →
      ∀ rate : ℝ, 0 < rate →
        (∀ π' : S → ℝ, IsStationary K π' → π' = π) ∧ AttractsAllStates K rate π := by
  intro S _ _ _ _ K hK V hV0 hVs C hC b hdrift z₀ hz₀ hacc π hπ rate hrate
  exact SC9aK4.k4_of_durrett
    (fun p hp hirr hap μ hμ x y => DurrettProbability.markov_convergence p hp hirr hap μ hμ x y)
    K hK V hV0 hVs C hC b hdrift z₀ hz₀ hacc π hπ rate hrate
