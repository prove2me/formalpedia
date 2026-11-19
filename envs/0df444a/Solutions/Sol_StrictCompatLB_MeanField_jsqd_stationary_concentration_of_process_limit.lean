-- Prove2me | solution 1 for StrictCompatLB.MeanField.jsqd_stationary_concentration_of_process_limit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:53:48.116736+00:00
-- url     : https://prove2.me/submissions/95c30cb8-0858-4b86-bb62-faa4fae94183

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SC77K9

open StrictCompatLB.MeanField

/-! Child K9 of the 77ae612d decomposition: a stationary law of the jump chain is preserved by
the uniformised process (Poisson mixture of the powers of the kernel). -/

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

lemma pn_sum (rate : ℝ) (hr : 0 < rate) (t : ℝ) :
    ∑' n : ℕ, (Measure.infinitePi (fun _ : ℕ => expMeasure rate))
      {s : ℕ → ℝ | epochCount s t = n} = 1 := by
  haveI : IsProbabilityMeasure (expMeasure rate) := isProbabilityMeasure_expMeasure hr
  have h := measure_iUnion (μ := Measure.infinitePi (fun _ : ℕ => expMeasure rate))
    (f := fun n : ℕ => {s : ℕ → ℝ | epochCount s t = n})
    (fun n m hnm => Set.disjoint_left.2 fun s
      (h1 : epochCount s t = n) (h2 : epochCount s t = m) => hnm (h1.symm.trans h2))
    (fun n => meas_ec t n)
  have hu : (⋃ n : ℕ, {s : ℕ → ℝ | epochCount s t = n}) = Set.univ := by
    ext s; simp
  rw [hu, measure_univ] at h
  exact h.symm

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

lemma event_formula {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {K : S → S → ℝ} {rate : ℝ}
    {z₀ : S} {Y : ℕ → Ω → S} {τ : ℕ → Ω → ℝ} (hU : IsUniformizedProcess P K rate z₀ Y τ)
    (hK : IsStochasticKernel K) (A : Set S) (t : ℝ) :
    P {ω | jumpPath (fun n => Y n ω) (fun k => τ k ω) t ∈ A} = ∑' n, (∑' z', A.indicator (Kn K n z₀) z') *
      (Measure.infinitePi (fun _ : ℕ => expMeasure rate)) {s : ℕ → ℝ | epochCount s t = n} := by
  haveI := hU.1
  have hYm : Measurable (fun ω n => Y n ω) := measurable_pi_lambda _ hU.2.1
  have hTm : Measurable (fun ω k => τ k ω) := measurable_pi_lambda _ hU.2.2.2.1
  have hA : MeasurableSet A := A.to_countable.measurableSet
  have hYA : ∀ n, MeasurableSet {y : ℕ → S | y n ∈ A} := fun n => measurable_pi_apply n hA
  have hlaw : P.map (fun ω k => τ k ω) = Measure.infinitePi (fun _ : ℕ => expMeasure rate) := by
    rw [(iIndepFun_iff_map_fun_eq_infinitePi_map (P := P) (X := τ) hU.2.2.2.1).1 hU.2.2.2.2.1]
    simp_rw [hU.2.2.2.2.2.1]
  have hset : {ω | jumpPath (fun n => Y n ω) (fun k => τ k ω) t ∈ A} = ⋃ n : ℕ, ((fun ω n => Y n ω) ⁻¹' {y : ℕ → S | y n ∈ A}
      ∩ (fun ω k => τ k ω) ⁻¹' {s : ℕ → ℝ | epochCount s t = n}) := by
    ext ω
    simp only [jumpPath, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨n, h, hn⟩; rw [hn]; exact h
  rw [hset, measure_iUnion]
  · congr 1; funext n
    rw [hU.2.2.2.2.2.2.measure_inter_preimage_eq_mul _ _ (hYA n) (meas_ec t n),
      ← Measure.map_apply hTm (meas_ec t n), hlaw]
    congr 1
    have h1 : (fun ω n => Y n ω) ⁻¹' {y : ℕ → S | y n ∈ A} = Y n ⁻¹' A := rfl
    rw [h1, ← Measure.map_apply (hU.2.1 n) hA, ← Measure.tsum_indicator_apply_singleton _ A hA]
    refine tsum_congr fun z' => ?_
    by_cases hz : z' ∈ A
    · simp only [Set.indicator_of_mem hz]
      rw [Measure.map_apply (hU.2.1 n) (measurableSet_singleton z')]
      exact marg1 hU hK n z'
    · simp [Set.indicator_of_notMem hz]
  · intro n m hnm
    refine Set.disjoint_left.2 fun ω h1 h2 => hnm ?_
    have e1 : epochCount (fun k => τ k ω) t = n := h1.2
    have e2 : epochCount (fun k => τ k ω) t = m := h2.2
    exact e1.symm.trans e2
  · intro n
    exact (hYm (hYA n)).inter (hTm (meas_ec t n))

lemma stat_iter (K : S → S → ℝ) (π : S → ℝ) (hπ : IsStationary K π) (hK : IsStochasticKernel K) :
    ∀ n z', ∑' z, ENNReal.ofReal (π z) * Kn K n z z' = ENNReal.ofReal (π z') := by
  intro n
  induction n with
  | zero =>
    intro z'
    simp only [Kn]
    rw [tsum_eq_single z' (fun b hb => by simp [Ne.symm hb])]
    simp
  | succ n ih =>
    intro z'
    simp only [Kn]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    simp_rw [← mul_assoc, ENNReal.tsum_mul_right, ih]
    simp_rw [← ENNReal.ofReal_mul (hπ.1.1 _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun y => mul_nonneg (hπ.1.1 y) (hK.1 y z'))
      (hπ.2 z').summable, (hπ.2 z').tsum_eq]

end Gen

theorem k9 (N : ℕ) (K : (Fin N → ℕ) → (Fin N → ℕ) → ℝ) (hK : IsStochasticKernel K)
    (rate : ℝ) (hr : 0 < rate) (π : (Fin N → ℕ) → ℝ) (hπ : IsStationary K π)
    (Ω : (Fin N → ℕ) → Type) [∀ z, MeasurableSpace (Ω z)] (P : ∀ z, Measure (Ω z))
    (Y : ∀ z, ℕ → Ω z → (Fin N → ℕ)) (τ : ∀ z, ℕ → Ω z → ℝ)
    (hU : ∀ z, IsUniformizedProcess (P z) K rate z (Y z) (τ z))
    (A : Set (Fin N → ℕ)) (t : ℝ) :
    ∑' z, π z * ((P z) {ω | statePath (Y z) (τ z) ω t ∈ A}).toReal = probOf π A := by
  have hform : ∀ z, (P z) {ω | statePath (Y z) (τ z) ω t ∈ A} = ∑' n,
      (∑' z', A.indicator (Kn K n z) z') *
      (Measure.infinitePi (fun _ : ℕ => expMeasure rate)) {s : ℕ → ℝ | epochCount s t = n} :=
    fun z => event_formula (hU z) hK A t
  have hfin : ∀ z, (P z) {ω | statePath (Y z) (τ z) ω t ∈ A} ≠ ∞ := fun z => by
    haveI := (hU z).1; exact measure_ne_top _ _
  have hL : ∑' z, π z * ((P z) {ω | statePath (Y z) (τ z) ω t ∈ A}).toReal =
      (∑' z, ENNReal.ofReal (π z) * (P z) {ω | statePath (Y z) (τ z) ω t ∈ A}).toReal := by
    rw [ENNReal.tsum_toReal_eq (fun z => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin z))]
    congr 1; funext z; rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hπ.1.1 z)]
  have hR : probOf π A = (∑' z, A.indicator (fun z => ENNReal.ofReal (π z)) z).toReal := by
    unfold probOf
    rw [ENNReal.tsum_toReal_eq (fun z => by unfold Set.indicator; split_ifs <;> simp)]
    congr 1; funext z; unfold Set.indicator; split_ifs <;> simp [hπ.1.1 z]
  rw [hL, hR]
  congr 1
  simp_rw [hform]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  have hinner : ∀ n, ∑' z, ENNReal.ofReal (π z) * ((∑' z', A.indicator (Kn K n z) z') *
      (Measure.infinitePi (fun _ : ℕ => expMeasure rate)) {s : ℕ → ℝ | epochCount s t = n}) =
      (∑' z', A.indicator (fun z => ENNReal.ofReal (π z)) z') *
      (Measure.infinitePi (fun _ : ℕ => expMeasure rate)) {s : ℕ → ℝ | epochCount s t = n} := by
    intro n
    have e1 : ∀ z, ENNReal.ofReal (π z) * ((∑' z', A.indicator (Kn K n z) z') *
        (Measure.infinitePi (fun _ : ℕ => expMeasure rate)) {s : ℕ → ℝ | epochCount s t = n}) =
        (∑' z', ENNReal.ofReal (π z) * A.indicator (Kn K n z) z') *
        (Measure.infinitePi (fun _ : ℕ => expMeasure rate)) {s : ℕ → ℝ | epochCount s t = n} :=
      fun z => by rw [ENNReal.tsum_mul_left]; ring
    rw [tsum_congr e1, ENNReal.tsum_mul_right, ENNReal.tsum_comm]
    congr 1
    refine tsum_congr fun z' => ?_
    by_cases hz : z' ∈ A
    · simp only [Set.indicator_of_mem hz]; exact stat_iter K π hπ hK n z'
    · simp [Set.indicator_of_notMem hz]
  simp_rw [hinner, ENNReal.tsum_mul_left, pn_sum rate hr t, mul_one]

end SC77K9


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SC77K10B

open StrictCompatLB.MeanField

/-- Pulling a uniformized process back along a measure-preserving map. -/
theorem transfer {S : Type} [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    (f : Ω → Ω') (hf : Measurable f) (hmap : P.map f = P')
    (K : S → S → ℝ) (rate : ℝ) (z₀ : S) (Y : ℕ → Ω' → S) (τ : ℕ → Ω' → ℝ)
    (h : IsUniformizedProcess P' K rate z₀ Y τ) :
    IsUniformizedProcess P K rate z₀ (fun n ω => Y n (f ω)) (fun k ω => τ k (f ω)) := by
  obtain ⟨hprob, hY, hcyl, hτ, hiid, hexp, hind⟩ := h
  have hmm : ∀ {β : Type _} [MeasurableSpace β] (g : Ω' → β), Measurable g →
      P.map (fun ω => g (f ω)) = P'.map g := by
    intro β _ g hg
    rw [← hmap, Measure.map_map hg hf]
    rfl
  have hP : IsProbabilityMeasure P := by
    constructor
    have := hprob.measure_univ
    rw [← hmap, Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ] at this
    exact this
  refine ⟨hP, fun n => (hY n).comp hf, fun n zs => ?_, fun k => (hτ k).comp hf, ?_,
    fun k => ?_, ?_⟩
  · have hms : MeasurableSet {ω' : Ω' | ∀ j ≤ n, Y j ω' = zs j} := by
      have : {ω' : Ω' | ∀ j ≤ n, Y j ω' = zs j} = ⋂ j, ⋂ (_ : j ≤ n), Y j ⁻¹' {zs j} := by
        ext; simp
      rw [this]
      exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        (hY j) (measurableSet_singleton _)
    rw [← hcyl n zs, ← hmap, Measure.map_apply hf hms]
    rfl
  · have hm : Measurable (fun ω' (k : ℕ) => τ k ω') := measurable_pi_lambda _ hτ
    refine (iIndepFun_iff_map_fun_eq_infinitePi_map₀' (X := fun k ω => τ k (f ω))
      (fun k => ((hτ k).comp hf).aemeasurable)).2 ?_
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀' (fun k => (hτ k).aemeasurable)] at hiid
    have e1 := hmm (fun ω' (k : ℕ) => τ k ω') hm
    have e2 : ∀ k, P.map (fun ω => τ k (f ω)) = P'.map (τ k) := fun k => hmm (τ k) (hτ k)
    rw [e1, hiid]
    simp_rw [e2]
  · rw [← hexp k]
    exact hmm (τ k) (hτ k)
  · have hmY : Measurable (fun ω' (n : ℕ) => Y n ω') := measurable_pi_lambda _ hY
    have hmτ : Measurable (fun ω' (k : ℕ) => τ k ω') := measurable_pi_lambda _ hτ
    show (fun ω (n : ℕ) => Y n (f ω)) ⟂ᵢ[P] (fun ω (k : ℕ) => τ k (f ω))
    refine (indepFun_iff_map_prod_eq_prod_map_map (f := fun ω (n : ℕ) => Y n (f ω))
      (g := fun ω (k : ℕ) => τ k (f ω)) (hmY.comp hf).aemeasurable
      (hmτ.comp hf).aemeasurable).2 ?_
    rw [indepFun_iff_map_prod_eq_prod_map_map hmY.aemeasurable hmτ.aemeasurable] at hind
    have h1 := hmm (fun ω' => ((fun n => Y n ω'), (fun k => τ k ω'))) (hmY.prodMk hmτ)
    have h2 := hmm (fun ω' (n : ℕ) => Y n ω') hmY
    have h3 := hmm (fun ω' (k : ℕ) => τ k ω') hmτ
    rw [h1, h2, h3]
    exact hind

/-- K10b: one probability space carrying the load-balancing processes for all `N ≥ 1` at once
(the product of the per-`N` spaces of K10 under `Measure.infinitePi`). -/
theorem k10b
    (hK10 : ∀ (lam : ℝ), 0 < lam → ∀ (M : ℕ → ℕ) (N : ℕ), 1 ≤ N →
      ∀ (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ),
        (∀ z, HasSum (lbKernel lam M N route z) 1) → (∀ z z', 0 ≤ lbKernel lam M N route z z') →
        ∀ z₀ : Fin N → ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
          (Y : ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → Ω → ℝ),
          IsLBProcess P lam M N route z₀ Y τ)
    (lam : ℝ) (hlam : 0 < lam) (M : ℕ → ℕ)
    (route : (N : ℕ) → Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (h1 : ∀ N, 1 ≤ N → ∀ z, HasSum (lbKernel lam M N (route N) z) 1)
    (h0 : ∀ N, 1 ≤ N → ∀ z z', 0 ≤ lbKernel lam M N (route N) z z')
    (z₀ : (N : ℕ) → Fin N → ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : (N : ℕ) → ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧
        ∀ N, 1 ≤ N → IsLBProcess P lam M N (route N) (z₀ N) (Y N) (τ N) := by
  have hex : ∀ N : ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (Y : ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ (1 ≤ N → IsLBProcess P lam M N (route N) (z₀ N) Y τ) := by
    intro N
    by_cases hN : 1 ≤ N
    · obtain ⟨Ω, mΩ, P, Y, τ, h⟩ :=
        hK10 lam hlam M N hN (route N) (h1 N hN) (h0 N hN) (z₀ N)
      exact ⟨Ω, mΩ, P, Y, τ, h.1, fun _ => h⟩
    · exact ⟨Unit, inferInstance, Measure.dirac (), fun _ _ => z₀ N, fun _ _ => 0,
        by infer_instance, fun h => absurd h hN⟩
  choose Ωf mΩf Pf Yf τf hf using hex
  let _ : ∀ N, MeasurableSpace (Ωf N) := mΩf
  have _ : ∀ N, IsProbabilityMeasure (Pf N) := fun N => (hf N).1
  refine ⟨(N : ℕ) → Ωf N, inferInstance, Measure.infinitePi Pf,
    fun N n ω => Yf N n (ω N), fun N k ω => τf N k (ω N), inferInstance, fun N hN => ?_⟩
  exact transfer (Measure.infinitePi Pf) (Pf N) (fun ω => ω N) (measurable_pi_apply N)
    (Measure.infinitePi_map_eval Pf N) _ _ _ _ _ ((hf N).2 hN)

end SC77K10B


set_option autoImplicit false

open Filter Topology
open scoped ENNReal

namespace SC77K11A

open StrictCompatLB.MeanField

/-! K11a: every `q ∈ 𝒴` is the ℓ¹ limit of occupancies of `N`-server states.
`z N v` = number of levels `i ≥ 1` with `(v+1)/N ≤ q i`, so `occ (z N) i = ⌊N q_i⌋ / N`. -/

variable (q : ℕ → ℝ)

lemma exists_small (hq : InY q) {N : ℕ} (v : Fin N) :
    ∃ i, q (i + 1) < ((v : ℝ) + 1) / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero (fun h => by subst h; exact v.elim0))
  have hpos : (0 : ℝ) < ((v : ℝ) + 1) / N := by positivity
  have ht : Tendsto (fun i => q (i + 1)) atTop (𝓝 0) := hq.2.tendsto_atTop_zero
  exact (ht.eventually (gt_mem_nhds hpos)).exists

open Classical in
noncomputable def zz (hq : InY q) (N : ℕ) : Fin N → ℕ :=
  fun v => Nat.find (exists_small q hq v)

lemma le_zz_iff (hq : InY q) {N : ℕ} (v : Fin N) (i : ℕ) :
    i + 1 ≤ zz q hq N v ↔ ((v : ℝ) + 1) / N ≤ q (i + 1) := by
  classical
  unfold zz
  rw [Nat.add_one_le_iff, Nat.lt_find_iff]
  constructor
  · intro h
    exact not_lt.mp (h i le_rfl)
  · intro h j hj
    have hanti : q (i + 1) ≤ q (j + 1) := hq.1.2.2 (by omega)
    exact not_lt.mpr (h.trans hanti)

lemma q_le_one (hq : InY q) (i : ℕ) : q i ≤ 1 := by
  have := hq.1.2.2 (Nat.zero_le i)
  rw [hq.1.1] at this
  exact this

lemma Qcount_succ (hq : InY q) {N : ℕ} (hN : 1 ≤ N) (i : ℕ) :
    (Qcount (zz q hq N) (i + 1) : ℝ) = ⌊(N : ℝ) * q (i + 1)⌋₊ := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hq0 : 0 ≤ q (i + 1) := hq.1.2.1 (i + 1)
  have hq1 : q (i + 1) ≤ 1 := q_le_one q hq (i + 1)
  have hset : (Finset.univ.filter (fun v : Fin N => i + 1 ≤ zz q hq N v)) =
      Finset.univ.filter (fun v : Fin N => (v : ℕ) < ⌊(N : ℝ) * q (i + 1)⌋₊) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [le_zz_iff, div_le_iff₀ hNr, Nat.lt_iff_add_one_le, Nat.le_floor_iff (by positivity),
      mul_comm]
    push_cast
    exact Iff.rfl
  have hfl : ⌊(N : ℝ) * q (i + 1)⌋₊ ≤ N := by
    apply Nat.floor_le_of_le
    nlinarith
  unfold Qcount
  rw [hset]
  have : (Finset.univ.filter (fun v : Fin N => (v : ℕ) < ⌊(N : ℝ) * q (i + 1)⌋₊)).card =
      ⌊(N : ℝ) * q (i + 1)⌋₊ := by
    rw [Fin.card_filter_val_lt]
    omega
  rw [this]

lemma Qcount_zero {N : ℕ} (z : Fin N → ℕ) : Qcount z 0 = N := by
  classical
  unfold Qcount
  simp

lemma err_bound (hq : InY q) {N : ℕ} (hN : 1 ≤ N) (i : ℕ) :
    |occ (zz q hq N) i - q i| ≤ if i = 0 then 0 else min (q i) (1 / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rcases i with _ | i
  · simp [occ, Qcount_zero, hq.1.1, hNr.ne']
  · simp only [Nat.add_one_ne_zero, if_false, occ]
    rw [Qcount_succ q hq hN i]
    have hq0 : 0 ≤ q (i + 1) := hq.1.2.1 (i + 1)
    set x := (N : ℝ) * q (i + 1) with hx
    have hx0 : 0 ≤ x := by positivity
    have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    have h2 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    have h3 : (0 : ℝ) ≤ ⌊x⌋₊ := Nat.cast_nonneg _
    have hqx : q (i + 1) = x / N := by rw [hx]; field_simp
    rw [hqx, ← sub_div, abs_div, abs_of_pos hNr, abs_of_nonpos (by linarith)]
    rw [le_min_iff]
    constructor
    · rw [div_le_div_iff_of_pos_right hNr]; linarith
    · rw [div_le_div_iff_of_pos_right hNr]; linarith

theorem k11a (hq : InY q) :
    ∃ z : (N : ℕ) → Fin N → ℕ,
      Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z N)) q) atTop (𝓝 0) := by
  refine ⟨zz q hq, ?_⟩
  let b : ℕ → ℝ := fun i => if i = 0 then 0 else q i
  have hb : Summable b := by
    have hs : Summable (fun i => q (i + 1)) := hq.2
    refine (summable_nat_add_iff 1).mp ?_
    simpa [b] using hs
  -- real error tends to zero
  have hreal : Tendsto (fun N : ℕ => ∑' i, |occ (zz q hq N) i - q i|) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => ∑' i, |occ (zz q hq N) i - q i|) atTop
        (𝓝 (∑' _i : ℕ, (0 : ℝ))) := by
      apply tendsto_tsum_of_dominated_convergence (bound := b) hb
      · intro i
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero_norm' ?_ (tendsto_one_div_atTop_nhds_zero_nat)
        filter_upwards [eventually_ge_atTop 1] with N hN
        rw [norm_norm, Real.norm_eq_abs, abs_abs]
        refine (err_bound q hq hN i).trans ?_
        split_ifs
        · positivity
        · exact min_le_right _ _
      · filter_upwards [eventually_ge_atTop 1] with N hN i
        rw [Real.norm_eq_abs, abs_abs]
        refine (err_bound q hq hN i).trans ?_
        simp only [b]
        split_ifs
        · exact le_rfl
        · exact min_le_left _ _
    simpa using hlim
  have hsum : ∀ N, 1 ≤ N → Summable (fun i => |occ (zz q hq N) i - q i|) := by
    intro N hN
    refine Summable.of_nonneg_of_le (fun i => abs_nonneg _) (fun i => ?_) hb
    refine (err_bound q hq hN i).trans ?_
    simp only [b]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have heq : ∀ᶠ N in atTop, PowerOfDUniversality.Fluid.l1dist (occ (zz q hq N)) q =
      ENNReal.ofReal (∑' i, |occ (zz q hq N) i - q i|) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    unfold PowerOfDUniversality.Fluid.l1dist
    rw [ENNReal.ofReal_tsum_of_nonneg (fun i => abs_nonneg _) (hsum N hN)]
  rw [tendsto_congr' heq, ← ENNReal.ofReal_zero]
  exact ENNReal.tendsto_ofReal hreal

end SC77K11A


namespace SC77K11

open StrictCompatLB.MeanField

/-- The weighted vector `(ω_{i+1} q_{i+1})_i` of `q` lies in `Kc ⊆ ℓ₁`. -/
def WIn (ω : ℕ → ℝ) (Kc : Set (lp (fun _ : ℕ => ℝ) 1)) (q : ℕ → ℝ) : Prop :=
  ∃ y ∈ Kc, ∀ i : ℕ, (y : ℕ → ℝ) i = ω (i + 1) * q (i + 1)

/-- K11c: uniform time after which every Y-valued trajectory started in the compact set is
within `ε` of the fixed point. -/
def K11c (lam : ℝ) (d : ℕ) (ω : ℕ → ℝ) : Prop :=
  ∀ Kc : Set (lp (fun _ : ℕ => ℝ) 1), IsCompact Kc → ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧
    ∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s → (∀ t, 0 ≤ t → InY (s t)) →
      WIn ω Kc (s 0) →
      PowerOfDUniversality.Fluid.l1dist (s T) (PowerTwoChoices.Limit.fixedPoint lam d) ≤
        ENNReal.ofReal ε

/-- The K10 statement (existence of a realisation of the load-balancing process). -/
def K10S : Prop :=
  ∀ (lam : ℝ), 0 < lam → ∀ (M : ℕ → ℕ) (N : ℕ), 1 ≤ N →
  ∀ (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ),
    (∀ z, HasSum (lbKernel lam M N route z) 1) → (∀ z z', 0 ≤ lbKernel lam M N route z z') →
    ∀ z₀ : Fin N → ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (Y : ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → Ω → ℝ),
      IsLBProcess P lam M N route z₀ Y τ

/-- K11 main: interchange of limits (arXiv 2008.07562, proof of Thm 3.4, p. 23). -/
def K11 : Prop :=
  ∀ (lam : ℝ), 0 < lam → lam < 1 → ∀ (d : ℕ), 2 ≤ d →
  ∀ (M : ℕ → ℕ), (∀ N, 0 < M N) → ∀ (G : (N : ℕ) → Finset (Fin N × Fin (M N))),
  (∀ N, 1 ≤ N → IsStochasticKernel (jsqdKernel lam d M G N)) →
  K10S →
  (∀ (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ), InY q₀ →
      Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0) →
      ∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s →
        (∀ t : ℝ, 0 ≤ t → InY (s t)) → s 0 = q₀ →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
          (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ),
          (∀ N, 1 ≤ N → IsLBProcess P lam M N (jsqdRoute M G N d) (z₀ N) (Y N) (τ N)) →
          ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
                PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T})
              atTop (𝓝 0)) →
  (∀ q₀ : ℕ → ℝ, InY q₀ → ∃ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s ∧
      (∀ t : ℝ, 0 ≤ t → InY (s t)) ∧ s 0 = q₀) →
  ∀ (ω : ℕ → ℝ) (c : ℝ), 0 < c → (∀ i, 1 ≤ i → c ≤ ω i) → K11c lam d ω →
  ∀ (N₀ : ℕ), 1 ≤ N₀ → ∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
    (∀ N ≥ N₀, IsStationary (jsqdKernel lam d M G N) (π N)) → IsTightWeighted ω N₀ π →
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => probOf (π N) {z | ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.l1dist (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)})
        atTop (𝓝 0)

lemma l1_triangle (x y z : ℕ → ℝ) :
    PowerOfDUniversality.Fluid.l1dist x z ≤
      PowerOfDUniversality.Fluid.l1dist x y + PowerOfDUniversality.Fluid.l1dist y z := by
  unfold PowerOfDUniversality.Fluid.l1dist
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

lemma l1_le_sup (x y : ℝ → ℕ → ℝ) {T : ℝ} (hT : 0 ≤ T) :
    PowerOfDUniversality.Fluid.l1dist (x T) (y T) ≤ PowerOfDUniversality.Fluid.supDistL1 x y T := by
  unfold PowerOfDUniversality.Fluid.supDistL1
  exact le_iSup₂_of_le T ⟨hT, le_rfl⟩ le_rfl

lemma half_le {a : ℝ≥0∞} {ε : ℝ} (hε : 0 < ε)
    (h : ENNReal.ofReal ε ≤ a + ENNReal.ofReal (ε / 2)) : ENNReal.ofReal (ε / 2) ≤ a := by
  by_contra hlt
  push_neg at hlt
  have h2 : a + ENNReal.ofReal (ε / 2) < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
    ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hlt
  rw [← ENNReal.ofReal_add (by linarith) (by linarith), add_halves] at h2
  exact absurd h (not_le.mpr h2)

lemma occ_zero {N : ℕ} (hN : 1 ≤ N) (z : Fin N → ℕ) : occ z 0 = 1 := by
  classical
  have h : Qcount z 0 = N := by unfold Qcount; simp
  unfold occ
  rw [h]
  exact div_self (Nat.cast_ne_zero.mpr (by omega))

lemma occ_nonneg {N : ℕ} (z : Fin N → ℕ) (i : ℕ) : 0 ≤ occ z i := by
  unfold occ
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma occ_anti {N : ℕ} (z : Fin N → ℕ) {i j : ℕ} (hij : i ≤ j) : occ z j ≤ occ z i := by
  classical
  unfold occ
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  unfold Qcount
  exact_mod_cast Finset.card_le_card (fun v hv => by
    simp only [Finset.mem_filter] at hv ⊢
    exact ⟨hv.1, le_trans hij hv.2⟩)

lemma norm_lp1 (a : lp (fun _ : ℕ => ℝ) 1) : ‖a‖ = ∑' i, |(a : ℕ → ℝ) i| := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : (0:ℝ) < (1 : ℝ≥0∞).toReal)]
  simp [Real.norm_eq_abs]

lemma summ_lp1 (a : lp (fun _ : ℕ => ℝ) 1) : Summable fun i => |(a : ℕ → ℝ) i| := by
  have := (lp.memℓp a).summable (by norm_num : (0:ℝ) < (1 : ℝ≥0∞).toReal)
  simpa [Real.norm_eq_abs] using this

lemma coord_le (a : lp (fun _ : ℕ => ℝ) 1) (i : ℕ) : |(a : ℕ → ℝ) i| ≤ ‖a‖ := by
  have := lp.norm_apply_le_norm (by norm_num : (1 : ℝ≥0∞) ≠ 0) a i
  simpa [Real.norm_eq_abs] using this

lemma occ_pt {ω : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (hω : ∀ i, 1 ≤ i → c ≤ ω i)
    (y y' : lp (fun _ : ℕ => ℝ) 1) {N : ℕ} (z : Fin N → ℕ)
    (hz : ∀ i, (y : ℕ → ℝ) i = ω (i + 1) * occ z (i + 1)) (q : ℕ → ℝ)
    (hq : ∀ i, (y' : ℕ → ℝ) i = ω (i + 1) * q (i + 1)) (i : ℕ) :
    |occ z (i + 1) - q (i + 1)| ≤ |(y : ℕ → ℝ) i - (y' : ℕ → ℝ) i| / c := by
  have hωp : 0 < ω (i + 1) := lt_of_lt_of_le hc (hω _ (by omega))
  have e : occ z (i + 1) - q (i + 1) = ((y : ℕ → ℝ) i - (y' : ℕ → ℝ) i) / ω (i + 1) := by
    rw [hz, hq, ← mul_sub, mul_comm, mul_div_assoc, div_self hωp.ne', mul_one]
  rw [e, abs_div, abs_of_pos hωp]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hc (hω _ (by omega))

lemma occ_close {ω : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (hω : ∀ i, 1 ≤ i → c ≤ ω i)
    (y y' : lp (fun _ : ℕ => ℝ) 1) {N : ℕ} (hN : 1 ≤ N) (z : Fin N → ℕ)
    (hz : ∀ i, (y : ℕ → ℝ) i = ω (i + 1) * occ z (i + 1)) (q : ℕ → ℝ) (hq0 : q 0 = 1)
    (hq : ∀ i, (y' : ℕ → ℝ) i = ω (i + 1) * q (i + 1)) :
    PowerOfDUniversality.Fluid.l1dist (occ z) q ≤ ENNReal.ofReal (‖y - y'‖ / c) := by
  have hS : Summable fun i => |(y : ℕ → ℝ) i - (y' : ℕ → ℝ) i| := by
    have := summ_lp1 (y - y'); simpa only [lp.coeFn_sub, Pi.sub_apply] using this
  have hN' : ‖y - y'‖ = ∑' i, |(y : ℕ → ℝ) i - (y' : ℕ → ℝ) i| := by
    rw [norm_lp1]; simp only [lp.coeFn_sub, Pi.sub_apply]
  unfold PowerOfDUniversality.Fluid.l1dist
  rw [tsum_eq_zero_add' ENNReal.summable, occ_zero hN, hq0, sub_self, abs_zero,
    ENNReal.ofReal_zero, zero_add, hN', ← tsum_div_const,
    ENNReal.ofReal_tsum_of_nonneg (fun i => div_nonneg (abs_nonneg _) hc.le) (hS.div_const c)]
  exact ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal (occ_pt hc hω y y' z hz q hq i)

/-- The Poisson-mixture formula for `P{Φ(t) ∈ A}` (independent of the realisation). -/
noncomputable def Qf {N : ℕ} (K : (Fin N → ℕ) → (Fin N → ℕ) → ℝ) (rate : ℝ) (z : Fin N → ℕ)
    (A : Set (Fin N → ℕ)) (t : ℝ) : ℝ≥0∞ :=
  ∑' n, (∑' z', A.indicator (SC77K9.Kn K n z) z') *
    (Measure.infinitePi (fun _ : ℕ => expMeasure rate)) {s : ℕ → ℝ | epochCount s t = n}

lemma Qf_eq {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {K : (Fin N → ℕ) → (Fin N → ℕ) → ℝ} {rate : ℝ} {z : Fin N → ℕ}
    {Y : ℕ → Ω → (Fin N → ℕ)} {τ : ℕ → Ω → ℝ}
    (hU : IsUniformizedProcess P K rate z Y τ) (hK : IsStochasticKernel K)
    (A : Set (Fin N → ℕ)) (t : ℝ) :
    P {ω | statePath Y τ ω t ∈ A} = Qf K rate z A t :=
  SC77K9.event_formula hU hK A t

lemma Qf_le_one {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {K : (Fin N → ℕ) → (Fin N → ℕ) → ℝ} {rate : ℝ} {z : Fin N → ℕ}
    {Y : ℕ → Ω → (Fin N → ℕ)} {τ : ℕ → Ω → ℝ}
    (hU : IsUniformizedProcess P K rate z Y τ) (hK : IsStochasticKernel K)
    (A : Set (Fin N → ℕ)) (t : ℝ) : (Qf K rate z A t).toReal ≤ 1 := by
  haveI := hU.1
  rw [← Qf_eq hU hK A t]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

lemma part_a (hK10 : K10S) {lam : ℝ} (hlam : 0 < lam) (M : ℕ → ℕ) {N : ℕ} (hN : 1 ≤ N)
    (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (hst : IsStochasticKernel (lbKernel lam M N route))
    (π : (Fin N → ℕ) → ℝ) (hπ : IsStationary (lbKernel lam M N route) π)
    (A : Set (Fin N → ℕ)) (t : ℝ) :
    ∑' z, π z * (Qf (lbKernel lam M N route) ((lam + 1) * N) z A t).toReal = probOf π A ∧
    ∀ z, (Qf (lbKernel lam M N route) ((lam + 1) * N) z A t).toReal ≤ 1 := by
  choose Ωf hmf Pf Yf τf hf using fun z => hK10 lam hlam M N hN route hst.2 hst.1 z
  have hr : 0 < (lam + 1) * (N : ℝ) := mul_pos (by linarith) (by exact_mod_cast hN)
  have key := SC77K9.k9 N (lbKernel lam M N route) hst ((lam + 1) * N) hr π hπ Ωf Pf Yf τf
    (fun z => hf z) A t
  refine ⟨?_, fun z => Qf_le_one (hf z) hst A t⟩
  rw [← key]
  congr 1
  funext z
  rw [Qf_eq (hf z) hst A t]

lemma split_bound {S : Type} (π : S → ℝ) (hπ : IsProbVec π) (Q : S → ℝ) (hQ0 : ∀ z, 0 ≤ Q z)
    (hQ1 : ∀ z, Q z ≤ 1) (G : Set S) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : ∀ z ∈ G, Q z ≤ δ) :
    ∑' z, π z * Q z ≤ δ + probOf π Gᶜ := by
  have hs : Summable π := hπ.2.summable
  have hg : Summable fun z => δ * π z + Gᶜ.indicator π z := (hs.mul_left δ).add (hs.indicator _)
  have hle : ∀ z, π z * Q z ≤ δ * π z + Gᶜ.indicator π z := by
    intro z
    by_cases hz : z ∈ G
    · rw [Set.indicator_of_notMem (by simpa using hz), add_zero, mul_comm δ]
      exact mul_le_mul_of_nonneg_left (hδ z hz) (hπ.1 z)
    · rw [Set.indicator_of_mem (by simpa using hz)]
      have := mul_le_mul_of_nonneg_left (hQ1 z) (hπ.1 z)
      linarith [mul_nonneg hδ0 (hπ.1 z)]
  have hf : Summable fun z => π z * Q z :=
    Summable.of_nonneg_of_le (fun z => mul_nonneg (hπ.1 z) (hQ0 z))
      (fun z => le_trans (mul_le_mul_of_nonneg_left (hQ1 z) (hπ.1 z)) (mul_one (π z)).le) hs
  calc ∑' z, π z * Q z ≤ ∑' z, (δ * π z + Gᶜ.indicator π z) := Summable.tsum_le_tsum hle hf hg
    _ = δ + probOf π Gᶜ := by
      rw [Summable.tsum_add (hs.mul_left δ) (hs.indicator _), tsum_mul_left, hπ.2.tsum_eq,
        mul_one]
      rfl

theorem k11 : K11 := by
  intro lam hlam hlam1 d hd M hM G hst hK10 hconj1 hK7 ω c hc hωc hK11c N₀ hN₀ π hπ htight ε hε
  classical
  set qs := PowerTwoChoices.Limit.fixedPoint lam d with hqs
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨Kc, hKc, htk⟩ := htight (δ / 4) (by linarith)
  obtain ⟨T, hT0, hTs⟩ := hK11c Kc hKc (ε / 2) (by linarith)
  let Bad : (N : ℕ) → Set (Fin N → ℕ) := fun N =>
    {z | ENNReal.ofReal ε ≤ PowerOfDUniversality.Fluid.l1dist (occ z) qs}
  let Q : (N : ℕ) → (Fin N → ℕ) → ℝ := fun N z =>
    (Qf (jsqdKernel lam d M G N) ((lam + 1) * N) z (Bad N) T).toReal
  have claim : ∀ᶠ N in atTop, ∀ z : Fin N → ℕ, WIn ω Kc (occ z) → Q N z ≤ δ / 4 := by
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    have hcon' : ∃ᶠ N in atTop, ∃ z : Fin N → ℕ, WIn ω Kc (occ z) ∧ δ / 4 < Q N z := by
      refine hcon.mono fun N hN => ?_
      push_neg at hN
      exact hN
    obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hcon'
    choose zk hzW hzQ using hφP
    unfold WIn at hzW
    choose yk hyK hyeq using hzW
    obtain ⟨ys, hysK, ψ, hψ, hlim⟩ := hKc.tendsto_subseq hyK
    have hmono : StrictMono (fun k => φ (ψ k)) := hφ.comp hψ
    have hge : ∀ k, k ≤ φ (ψ k) := fun k => hmono.id_le k
    have hωpos : ∀ i, 1 ≤ i → 0 < ω i := fun i hi => lt_of_lt_of_le hc (hωc i hi)
    let q₀ : ℕ → ℝ := fun i => if i = 0 then 1 else (ys : ℕ → ℝ) (i - 1) / ω i
    have hq₀0 : q₀ 0 = 1 := by simp [q₀]
    have hq₀s : ∀ i, q₀ (i + 1) = (ys : ℕ → ℝ) i / ω (i + 1) := fun i => by simp [q₀]
    have hq₀w : ∀ i, (ys : ℕ → ℝ) i = ω (i + 1) * q₀ (i + 1) := fun i => by
      rw [hq₀s, mul_comm, div_mul_cancel₀ _ (hωpos (i + 1) (by omega)).ne']
    have hnorm : Tendsto (fun k => ‖yk (ψ k) - ys‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hlim
    have hdiv : Tendsto (fun k => ‖yk (ψ k) - ys‖ / c) atTop (𝓝 0) := by
      simpa using hnorm.div_const c
    have hpt : ∀ k, 1 ≤ k → ∀ i, |occ (zk (ψ k)) i - q₀ i| ≤ ‖yk (ψ k) - ys‖ / c := by
      intro k hk i
      have hN1 : 1 ≤ φ (ψ k) := le_trans hk (hge k)
      rcases i with _ | i
      · rw [occ_zero hN1, hq₀0, sub_self, abs_zero]; exact div_nonneg (norm_nonneg _) hc.le
      · refine le_trans (occ_pt hc hωc (yk (ψ k)) ys (zk (ψ k)) (hyeq (ψ k)) q₀ hq₀w i) ?_
        refine div_le_div_of_nonneg_right ?_ hc.le
        have := coord_le (yk (ψ k) - ys) i
        simpa only [lp.coeFn_sub, Pi.sub_apply] using this
    have hconv : ∀ i, Tendsto (fun k => occ (zk (ψ k)) i) atTop (𝓝 (q₀ i)) := by
      intro i
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hdiv
      filter_upwards [eventually_ge_atTop 1] with k hk
      rw [Real.norm_eq_abs]
      exact hpt k hk i
    have hq₀nn : ∀ i, 0 ≤ q₀ i := fun i =>
      ge_of_tendsto' (hconv i) fun k => occ_nonneg _ i
    have hq₀Y : InY q₀ := by
      refine ⟨⟨hq₀0, hq₀nn, ?_⟩, ?_⟩
      · intro i j hij
        exact le_of_tendsto_of_tendsto' (hconv j) (hconv i) fun k => occ_anti _ hij
      · refine Summable.of_nonneg_of_le (fun i => hq₀nn (i + 1)) (fun i => ?_)
          ((summ_lp1 ys).div_const c)
        rw [hq₀s]
        calc (ys : ℕ → ℝ) i / ω (i + 1) ≤ |(ys : ℕ → ℝ) i| / ω (i + 1) :=
              div_le_div_of_nonneg_right (le_abs_self _) (hωpos _ (by omega)).le
          _ ≤ |(ys : ℕ → ℝ) i| / c :=
              div_le_div_of_nonneg_left (abs_nonneg _) hc (hωc _ (by omega))
    obtain ⟨za, hza⟩ := SC77K11A.k11a q₀ hq₀Y
    let z0' : (N : ℕ) → Fin N → ℕ := fun N v =>
      if h : ∃ k, φ (ψ k) = N then zk (ψ h.choose) (Fin.cast h.choose_spec.symm v) else za N v
    have hcast : ∀ k k' (_ : k' = k) (h' : φ (ψ k') = φ (ψ k)) (v : Fin (φ (ψ k))),
        zk (ψ k') (Fin.cast h'.symm v) = zk (ψ k) v := by
      intro k k' e
      subst e
      intro h' v
      exact congrArg _ (Fin.ext rfl)
    have hz0' : ∀ k, z0' (φ (ψ k)) = zk (ψ k) := by
      intro k
      funext v
      have h : ∃ k', φ (ψ k') = φ (ψ k) := ⟨k, rfl⟩
      simp only [z0', dif_pos h]
      exact hcast k h.choose (hmono.injective h.choose_spec) h.choose_spec v
    have hz0conv :
        Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z0' N)) q₀) atTop (𝓝 0) := by
      have hA : Tendsto (fun k => ENNReal.ofReal (‖yk (ψ k) - ys‖ / c)) atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal hdiv
      rw [ENNReal.tendsto_atTop_zero] at hA hza ⊢
      intro e he
      obtain ⟨K1, hK1⟩ := hA e he
      obtain ⟨N1, hN1⟩ := hza e he
      refine ⟨max N1 (φ (ψ (max K1 1))), fun N hN => ?_⟩
      by_cases h : ∃ k, φ (ψ k) = N
      · obtain ⟨k, rfl⟩ := h
        have hk : max K1 1 ≤ k := by
          by_contra hlt
          push_neg at hlt
          have h1 : φ (ψ k) < φ (ψ (max K1 1)) := hmono hlt
          have h2 := le_trans (le_max_right _ _) hN
          omega
        rw [hz0' k]
        exact le_trans (occ_close hc hωc (yk (ψ k)) ys
          (le_trans (le_trans (le_max_right _ _) hk) (hge k)) (zk (ψ k)) (hyeq (ψ k)) q₀ hq₀0 hq₀w)
          (hK1 k (le_trans (le_max_left _ _) hk))
      · have hz : z0' N = za N := by
          funext v
          simp only [z0', dif_neg h]
        rw [hz]
        exact hN1 N (le_trans (le_max_left _ _) hN)
    obtain ⟨s, hs, hsY, hs0⟩ := hK7 q₀ hq₀Y
    have hsT : PowerOfDUniversality.Fluid.l1dist (s T) qs ≤ ENNReal.ofReal (ε / 2) :=
      hTs s hs hsY (by rw [hs0]; exact ⟨ys, hysK, hq₀w⟩)
    obtain ⟨Ω, _, P, Y, τ, _, hLB⟩ := SC77K10B.k10b hK10 lam hlam M
      (fun N => jsqdRoute M G N d) (fun N hN => (hst N hN).2) (fun N hN => (hst N hN).1) z0'
    have hc1 := hconj1 z0' q₀ hq₀Y hz0conv s hs hsY hs0 Ω P Y τ hLB T hT0 (ε / 2) (by linarith)
    rw [ENNReal.tendsto_atTop_zero] at hc1
    obtain ⟨N3, hN3⟩ := hc1 (ENNReal.ofReal (δ / 8)) (ENNReal.ofReal_pos.mpr (by linarith))
    obtain ⟨k, hk1, hk2⟩ : ∃ k, N3 ≤ k ∧ 1 ≤ k := ⟨max N3 1, le_max_left _ _, le_max_right _ _⟩
    have hN1 : 1 ≤ φ (ψ k) := le_trans hk2 (hge k)
    have hU : IsUniformizedProcess P (jsqdKernel lam d M G (φ (ψ k)))
        ((lam + 1) * ((φ (ψ k) : ℕ) : ℝ)) (zk (ψ k)) (Y (φ (ψ k))) (τ (φ (ψ k))) := by
      have h := hLB (φ (ψ k)) hN1
      rw [hz0' k] at h
      exact h
    have hQ := hzQ (ψ k)
    have heq := Qf_eq hU (hst _ hN1) (Bad (φ (ψ k))) T
    have hsub : {x | statePath (Y (φ (ψ k))) (τ (φ (ψ k))) x T ∈ Bad (φ (ψ k))} ⊆
        {x | ENNReal.ofReal (ε / 2) ≤ PowerOfDUniversality.Fluid.supDistL1
          (occPath (Y (φ (ψ k))) (τ (φ (ψ k))) x) s T} := by
      intro x hx
      simp only [Set.mem_setOf_eq]
      apply half_le hε
      calc ENNReal.ofReal ε
          ≤ PowerOfDUniversality.Fluid.l1dist
              (occ (statePath (Y (φ (ψ k))) (τ (φ (ψ k))) x T)) qs := hx
        _ ≤ PowerOfDUniversality.Fluid.l1dist (occPath (Y (φ (ψ k))) (τ (φ (ψ k))) x T) (s T) +
              PowerOfDUniversality.Fluid.l1dist (s T) qs := l1_triangle _ _ _
        _ ≤ PowerOfDUniversality.Fluid.supDistL1 (occPath (Y (φ (ψ k))) (τ (φ (ψ k))) x) s T +
              ENNReal.ofReal (ε / 2) := add_le_add (l1_le_sup _ _ hT0) hsT
    have hle : Qf (jsqdKernel lam d M G (φ (ψ k))) ((lam + 1) * ((φ (ψ k) : ℕ) : ℝ)) (zk (ψ k))
        (Bad (φ (ψ k))) T ≤ ENNReal.ofReal (δ / 8) := by
      rw [← heq]
      exact le_trans (measure_mono hsub) (hN3 (φ (ψ k)) (le_trans hk1 (hge k)))
    have h8 := ENNReal.toReal_le_of_le_ofReal (by linarith) hle
    have : δ / 4 < δ / 8 := lt_of_lt_of_le hQ h8
    linarith
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp claim
  refine ⟨max (max N₀ 1) N2, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hNN₀ : N ≥ N₀ := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNN2 : N ≥ N2 := le_trans (le_max_right _ _) hN
  obtain ⟨hpa, hle1⟩ := part_a hK10 hlam M hN1 (jsqdRoute M G N d) (hst N hN1) (π N)
    (hπ N hNN₀) (Bad N) T
  have hpa' : ∑' z, π N z * Q N z = probOf (π N) (Bad N) := hpa
  have hsb := split_bound (π N) (hπ N hNN₀).1 (fun z => Q N z) (fun z => ENNReal.toReal_nonneg)
    hle1 {z | WIn ω Kc (occ z)} (δ / 4) (by linarith) (fun z hz => hN2 N hNN2 z hz)
  have hpt : probOf (π N) {z | WIn ω Kc (occ z)}ᶜ ≤ δ / 4 := htk N hNN₀
  have hp0 : 0 ≤ probOf (π N) (Bad N) := by
    unfold probOf
    exact tsum_nonneg fun z => Set.indicator_nonneg (fun a _ => (hπ N hNN₀).1.1 a) z
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hp0]
  have hfin : probOf (π N) (Bad N) ≤ δ / 4 + δ / 4 := by
    rw [← hpa']
    linarith
  linarith

end SC77K11

namespace SC77K11C

open StrictCompatLB.MeanField

noncomputable def fw (lam : ℝ) (d : ℕ) (ω : ℕ → ℝ) (i : ℕ) : ℝ :=
  if 1 ≤ i then ω i * PowerTwoChoices.Limit.fixedPoint lam d i else 0

theorem k11c (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam < 1) (d : ℕ) (hd : 2 ≤ d)
    (ω : ℕ → ℝ) (hω : ∀ i, 1 ≤ i → 0 < ω i) (r : ℝ) (hr1 : 1 < r) (hr2 : r < 2 / (1 + lam))
    (i₀ : ℕ) (h417 : ∀ i : ℕ, 1 ≤ i → ω (i₀ + i) = ω i₀ * r ^ i)
    (δ : ℝ) (hδ : 0 < δ)
    (hdec : ∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s →
      (∀ t : ℝ, 0 ≤ t → InY (s t)) → ∀ t : ℝ, 0 ≤ t →
        PowerTwoChoices.Limit.potential lam d ω (s t) ≤
          ENNReal.ofReal (Real.exp (-δ * t)) * PowerTwoChoices.Limit.potential lam d ω (s 0)) :
    ∃ c : ℝ, 0 < c ∧ (∀ i, 1 ≤ i → c ≤ ω i) ∧ SC77K11.K11c lam d ω := by
  have hωi0 : 0 ≤ ω i₀ := by
    have h1 := h417 1 le_rfl
    have h2 := hω (i₀ + 1) (by omega)
    rw [h1, pow_one] at h2
    by_contra hneg
    push_neg at hneg
    nlinarith
  -- the lower bound c
  let c : ℝ := (Finset.Icc 1 (i₀ + 1)).inf' ⟨1, by simp⟩ ω
  have hc : 0 < c := (Finset.lt_inf'_iff _).mpr fun i hi => hω i (Finset.mem_Icc.mp hi).1
  have hcω : ∀ i, 1 ≤ i → c ≤ ω i := by
    intro i hi
    by_cases h : i ≤ i₀ + 1
    · exact Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hi, h⟩)
    · obtain ⟨j, rfl⟩ : ∃ j, i = i₀ + j := ⟨i - i₀, by omega⟩
      have hle : c ≤ ω (i₀ + 1) := Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
      rw [h417 1 le_rfl, pow_one] at hle
      rw [h417 j (by omega)]
      refine le_trans hle (mul_le_mul_of_nonneg_left ?_ hωi0)
      calc r = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ j := pow_le_pow_right₀ hr1.le (by omega)
  refine ⟨c, hc, hcω, ?_⟩
  -- the fixed point
  have hq0 : PowerTwoChoices.Limit.fixedPoint lam d 0 = 1 := by
    simp [PowerTwoChoices.Limit.fixedPoint]
  have hqs_nn : ∀ i, 0 ≤ PowerTwoChoices.Limit.fixedPoint lam d i := fun i => by
    unfold PowerTwoChoices.Limit.fixedPoint; exact pow_nonneg hlam.le _
  have hqs_le : ∀ i, PowerTwoChoices.Limit.fixedPoint lam d i ≤ lam ^ i := by
    intro i
    unfold PowerTwoChoices.Limit.fixedPoint
    apply pow_le_pow_of_le_one hlam.le hlam1.le
    calc i = ∑ k ∈ Finset.range i, 1 := by simp
      _ ≤ ∑ k ∈ Finset.range i, d ^ k :=
          Finset.sum_le_sum fun k _ => Nat.one_le_pow _ _ (by omega)
  have hrl : r * lam < 1 := by
    have h := hr2
    rw [lt_div_iff₀ (by linarith)] at h
    nlinarith
  have hrl0 : 0 ≤ r * lam := (mul_pos (by linarith) hlam).le
  have hf_nn : ∀ i, 0 ≤ fw lam d ω i := fun i => by
    unfold fw
    split_ifs with h
    · exact mul_nonneg (hω i h).le (hqs_nn i)
    · exact le_rfl
  have hf_sum : Summable (fw lam d ω) := by
    rw [← summable_nat_add_iff i₀]
    refine Summable.of_nonneg_of_le (fun j => hf_nn _) (fun j => ?_)
      ((summable_geometric_of_lt_one hrl0 hrl).mul_left (ω i₀))
    have hωj : ω (j + i₀) ≤ ω i₀ * r ^ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp
      · rw [add_comm, h417 j hj]
    unfold fw
    split_ifs with h
    · calc ω (j + i₀) * PowerTwoChoices.Limit.fixedPoint lam d (j + i₀)
          ≤ (ω i₀ * r ^ j) * lam ^ j := by
            apply mul_le_mul hωj _ (hqs_nn _) (mul_nonneg hωi0 (pow_nonneg (by linarith) _))
            exact le_trans (hqs_le _) (pow_le_pow_of_le_one hlam.le hlam1.le (by omega))
        _ = ω i₀ * (r * lam) ^ j := by rw [mul_pow]; ring
    · exact mul_nonneg hωi0 (pow_nonneg hrl0 _)
  set C : ℝ := ∑' i, fw lam d ω i with hC
  have hC0 : 0 ≤ C := tsum_nonneg hf_nn
  -- l1 distance controlled by the potential
  have hl1 : ∀ x : ℕ → ℝ, InY x →
      PowerOfDUniversality.Fluid.l1dist x (PowerTwoChoices.Limit.fixedPoint lam d) ≤
        (ENNReal.ofReal c)⁻¹ * PowerTwoChoices.Limit.potential lam d ω x := by
    intro x hx
    unfold PowerOfDUniversality.Fluid.l1dist PowerTwoChoices.Limit.potential
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun i => ?_
    rcases i with _ | j
    · rw [hx.1.1, hq0]; simp
    · rw [if_pos (by omega : 1 ≤ j + 1), ← ENNReal.ofReal_inv_of_pos hc,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
      apply ENNReal.ofReal_le_ofReal
      have h1 : 1 ≤ c⁻¹ * ω (j + 1) := by
        rw [le_inv_mul_iff₀ hc, mul_one]; exact hcω _ (by omega)
      have h2 := mul_le_mul_of_nonneg_right h1
        (abs_nonneg (x (j + 1) - PowerTwoChoices.Limit.fixedPoint lam d (j + 1)))
      rw [← mul_assoc]
      linarith
  -- potential bounded on the compact set
  have hpot0 : ∀ (Kc : Set (lp (fun _ : ℕ => ℝ) 1)) (R : ℝ), (∀ y ∈ Kc, ‖y‖ ≤ R) →
      ∀ x : ℕ → ℝ, InY x → SC77K11.WIn ω Kc x →
      PowerTwoChoices.Limit.potential lam d ω x ≤ ENNReal.ofReal (R + C) := by
    rintro Kc R hR x hx ⟨y, hyK, hyx⟩
    have hpt : ∀ i, (if 1 ≤ i then ENNReal.ofReal
          (ω i * |x i - PowerTwoChoices.Limit.fixedPoint lam d i|) else 0)
        ≤ (if 1 ≤ i then ENNReal.ofReal |(y : ℕ → ℝ) (i - 1)| else 0) +
          ENNReal.ofReal (fw lam d ω i) := by
      intro i
      rcases i with _ | j
      · simp
      · have h1 : 1 ≤ j + 1 := by omega
        rw [if_pos h1, if_pos h1, ← ENNReal.ofReal_add (abs_nonneg _) (hf_nn _)]
        apply ENNReal.ofReal_le_ofReal
        have hfj : fw lam d ω (j + 1) =
            ω (j + 1) * PowerTwoChoices.Limit.fixedPoint lam d (j + 1) := if_pos h1
        rw [hfj, Nat.add_sub_cancel, hyx j,
          abs_of_nonneg (mul_nonneg (hω _ h1).le (hx.1.2.1 _))]
        have hab : |x (j + 1) - PowerTwoChoices.Limit.fixedPoint lam d (j + 1)| ≤
            x (j + 1) + PowerTwoChoices.Limit.fixedPoint lam d (j + 1) :=
          abs_sub_le_iff.mpr ⟨by linarith [hqs_nn (j + 1)], by linarith [hx.1.2.1 (j + 1)]⟩
        calc ω (j + 1) * |x (j + 1) - PowerTwoChoices.Limit.fixedPoint lam d (j + 1)|
            ≤ ω (j + 1) * (x (j + 1) + PowerTwoChoices.Limit.fixedPoint lam d (j + 1)) :=
              mul_le_mul_of_nonneg_left hab (hω _ h1).le
          _ = _ := by ring
    unfold PowerTwoChoices.Limit.potential
    refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
    rw [ENNReal.tsum_add, tsum_eq_zero_add' ENNReal.summable, if_neg (by omega), zero_add,
      ← ENNReal.ofReal_tsum_of_nonneg hf_nn hf_sum, ← hC,
      ENNReal.ofReal_add (le_trans (norm_nonneg y) (hR y hyK)) hC0]
    gcongr
    have e : ∀ j : ℕ, (if 1 ≤ j + 1 then ENNReal.ofReal |(y : ℕ → ℝ) (j + 1 - 1)| else 0) =
        ENNReal.ofReal |(y : ℕ → ℝ) j| := fun j => by rw [if_pos (by omega), Nat.add_sub_cancel]
    rw [tsum_congr e, ← ENNReal.ofReal_tsum_of_nonneg (fun j => abs_nonneg _)
      (SC77K11.summ_lp1 y), ← SC77K11.norm_lp1]
    exact ENNReal.ofReal_le_ofReal (hR y hyK)
  -- the uniform time
  intro Kc hKc ε hε
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  set R' : ℝ := max R 0 with hR'
  have hR'b : ∀ y ∈ Kc, ‖y‖ ≤ R' := fun y hy => le_trans (hR y hy) (le_max_left _ _)
  set B : ℝ := c⁻¹ * (R' + C) with hB
  have hB0 : 0 ≤ B := mul_nonneg (inv_nonneg.mpr hc.le) (add_nonneg (le_max_right _ _) hC0)
  have hBe : 0 < B / ε + 1 := by have := div_nonneg hB0 hε.le; linarith
  refine ⟨Real.log (B / ε + 1) / δ,
    div_nonneg (Real.log_nonneg (by have := div_nonneg hB0 hε.le; linarith)) hδ.le, ?_⟩
  intro s hs hsY hW
  set T : ℝ := Real.log (B / ε + 1) / δ with hT
  have hT0 : 0 ≤ T := div_nonneg (Real.log_nonneg (by have := div_nonneg hB0 hε.le; linarith)) hδ.le
  have hexp : Real.exp (-δ * T) = (B / ε + 1)⁻¹ := by
    have : δ * T = Real.log (B / ε + 1) := by rw [hT]; field_simp
    rw [neg_mul, this, Real.exp_neg, Real.exp_log hBe]
  set X : ℝ := (B / ε + 1)⁻¹ with hXd
  have hXp : 0 < X := inv_pos.mpr hBe
  have hX1 : X * (B / ε + 1) = 1 := inv_mul_cancel₀ hBe.ne'
  have hXB : X * B ≤ ε := by
    have h1 : X * (B / ε) = 1 - X := by linarith [mul_add X (B / ε) 1]
    have h2 : X * B = ε * (X * (B / ε)) := by field_simp
    rw [h2, h1]
    nlinarith
  calc PowerOfDUniversality.Fluid.l1dist (s T) (PowerTwoChoices.Limit.fixedPoint lam d)
      ≤ (ENNReal.ofReal c)⁻¹ * PowerTwoChoices.Limit.potential lam d ω (s T) :=
        hl1 _ (hsY T hT0)
    _ ≤ (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal (Real.exp (-δ * T)) * ENNReal.ofReal (R' + C)) := by
        gcongr
        exact le_trans (hdec s hs hsY T hT0)
          (by gcongr; exact hpot0 Kc R' hR'b (s 0) (hsY 0 le_rfl) hW)
    _ = ENNReal.ofReal (X * B) := by
        rw [hexp, ← ENNReal.ofReal_inv_of_pos hc, ← ENNReal.ofReal_mul (inv_pos.mpr hBe).le,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), hB]
        congr 1
        ring
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hXB

end SC77K11C

open MeasureTheory ProbabilityTheory Filter Topology StrictCompatLB.MeanField in
theorem solution : ∀ (lam : ℝ), 0 < lam → lam < 1 → ∀ (d : ℕ), 2 ≤ d →
  ∀ (M : ℕ → ℕ), (∀ N, 0 < M N) → ∀ (G : (N : ℕ) → Finset (Fin N × Fin (M N))),
  (∀ N, 1 ≤ N → IsStochasticKernel (jsqdKernel lam d M G N)) →
  (∀ (lam' : ℝ), 0 < lam' → ∀ (M' : ℕ → ℕ) (N : ℕ), 1 ≤ N →
    ∀ (route : Fin (M' N) → (Fin N → ℕ) → Fin N → ℝ),
      (∀ z, HasSum (lbKernel lam' M' N route z) 1) → (∀ z z', 0 ≤ lbKernel lam' M' N route z z') →
      ∀ z₀ : Fin N → ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (Y : ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → Ω → ℝ),
        IsLBProcess P lam' M' N route z₀ Y τ) →
  (∀ (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ), InY q₀ →
      Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0) →
      ∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s →
        (∀ t : ℝ, 0 ≤ t → InY (s t)) → s 0 = q₀ →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
          (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ),
          (∀ N, 1 ≤ N → IsLBProcess P lam M N (jsqdRoute M G N d) (z₀ N) (Y N) (τ N)) →
          ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
                PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T})
              atTop (𝓝 0)) →
  (∀ q₀ : ℕ → ℝ, InY q₀ → ∃ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s ∧
      (∀ t : ℝ, 0 ≤ t → InY (s t)) ∧ s 0 = q₀) →
  ∀ (ω : ℕ → ℝ), (∀ i, 1 ≤ i → 0 < ω i) → ∀ (r : ℝ), 1 < r → r < 2 / (1 + lam) →
  ∀ (i₀ : ℕ), (∀ i : ℕ, 1 ≤ i → ω (i₀ + i) = ω i₀ * r ^ i) →
  ∀ (δ : ℝ), 0 < δ → (∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s →
      (∀ t : ℝ, 0 ≤ t → InY (s t)) → ∀ t : ℝ, 0 ≤ t →
        PowerTwoChoices.Limit.potential lam d ω (s t) ≤
          ENNReal.ofReal (Real.exp (-δ * t)) * PowerTwoChoices.Limit.potential lam d ω (s 0)) →
  ∀ (N₀ : ℕ), 1 ≤ N₀ → ∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
    (∀ N ≥ N₀, IsStationary (jsqdKernel lam d M G N) (π N)) → IsTightWeighted ω N₀ π →
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => probOf (π N) {z | ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.l1dist (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)})
        atTop (𝓝 0) := by
  intro lam hlam hlam1 d hd M hM G hst hK10 hconj hex ω hω r hr1 hr2 i₀ h417 δ hδ hdec
  obtain ⟨c, hc, hcω, hK11c⟩ := SC77K11C.k11c lam hlam hlam1 d hd ω hω r hr1 hr2 i₀ h417 δ hδ hdec
  exact SC77K11.k11 lam hlam hlam1 d hd M hM G hst hK10 hconj hex ω c hc hcω hK11c
