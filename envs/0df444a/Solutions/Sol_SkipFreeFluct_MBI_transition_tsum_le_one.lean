-- Prove2me | solution 1 for SkipFreeFluct.MBI.transition_tsum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T10:47:04.528992+00:00
-- url     : https://prove2.me/submissions/1b6b73e8-2c93-4632-9a1a-ac48ad9a5a19

import Mathlib
import Definitions.Def_SkipFreeFluct_MBI_Chain
open scoped ENNReal Topology
open Filter MeasureTheory

namespace TransLe1
open SkipFreeFluct.MBI ProbabilityTheory Classical

instance instProbExp : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

instance instProbClock (n : ℕ) : IsProbabilityMeasure (clockLaw n) := by
  unfold clockLaw; infer_instance

lemma measurable_holdTime (Q : ℤ → ℤ → ℝ) {n : ℕ} (ω : Fin (n + 1) → ℤ) (k : Fin (n + 1)) :
    Measurable (fun e => holdTime Q ω e k) := by
  unfold holdTime
  exact (ENNReal.measurable_ofReal.comp (measurable_pi_apply k)).div_const _

lemma measurable_jumpTime (Q : ℤ → ℤ → ℝ) {n : ℕ} (ω : Fin (n + 1) → ℤ) :
    Measurable (fun e => jumpTime Q ω e) := by
  unfold jumpTime
  exact Finset.measurable_sum _ fun k _ => measurable_holdTime Q ω _

/-- Splitting `{J_n ≤ T}` according to whether the next jump has happened by time `T`. -/
lemma split_event (Q : ℤ → ℤ → ℝ) {n : ℕ} (ω : Fin (n + 1) → ℤ) (T : ℝ≥0∞) :
    clockLaw n {e | jumpTime Q ω e ≤ T ∧ T < jumpTime Q ω e + holdTime Q ω e (Fin.last n)} +
      clockLaw n {e | jumpTime Q ω e + holdTime Q ω e (Fin.last n) ≤ T} =
    clockLaw n {e | jumpTime Q ω e ≤ T} := by
  rw [← measure_union]
  · congr 1
    ext e
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact le_trans le_self_add h
    · intro h
      rcases lt_or_ge T (jumpTime Q ω e + holdTime Q ω e (Fin.last n)) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr h'
  · rw [Set.disjoint_left]
    rintro e ⟨_, h1⟩ h2
    exact absurd h2 (not_le.mpr h1)
  · exact measurableSet_le ((measurable_jumpTime Q ω).add (measurable_holdTime Q ω _))
      measurable_const

/-- The marginal of `n + 2` clocks on the first `n + 1` coordinates. -/
lemma clockLaw_init (n : ℕ) (A : Set (Fin (n + 1) → ℝ)) (hA : MeasurableSet A) :
    clockLaw (n + 1) {e | Fin.init e ∈ A} = clockLaw n A := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 2) => expMeasure 1)
    (Fin.last (n + 1))
  have hset : {e : Fin (n + 2) → ℝ | Fin.init e ∈ A} =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) (Fin.last (n + 1))) ⁻¹'
        (Set.univ ×ˢ A) := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    have : (fun j => e ((Fin.last (n + 1)).succAbove j)) = Fin.init e := by
      funext j; simp [Fin.init, Fin.succAbove_last]
    simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.removeNth, this]
  unfold clockLaw
  rw [hset, hmp.measure_preimage (MeasurableSet.univ.prod hA).nullMeasurableSet,
    Measure.prod_prod, measure_univ, one_mul]

lemma jumpProb_tsum_le_one (E : Set ℤ) (Q : ℤ → ℤ → ℝ) (hQ : IsQMatrix E Q) (w : ℤ) :
    ∑' z : ℤ, jumpProb E Q w z ≤ 1 := by
  by_cases hw : w ∈ E ∧ 0 < rate Q w
  swap
  · have : ∀ z, jumpProb E Q w z = 0 := fun z => by
      unfold jumpProb; rw [if_neg]; tauto
    simp [this]
  obtain ⟨hwE, hr⟩ := hw
  set f : ℤ → ℝ := fun z => if z ∈ E ∧ z ≠ w then Q w z / rate Q w else 0 with hf
  have hf0 : ∀ z, 0 ≤ f z := fun z => by
    simp only [hf]; split_ifs with h
    · exact div_nonneg (hQ.1 w hwE z h.1 (Ne.symm h.2)) hr.le
    · exact le_rfl
  have hjp : ∀ z, jumpProb E Q w z = ENNReal.ofReal (f z) := fun z => by
    unfold jumpProb; simp only [hf]
    by_cases h : z ∈ E ∧ z ≠ w
    · rw [if_pos ⟨hwE, h.1, h.2, hr⟩, if_pos h]
    · rw [if_neg (by tauto), if_neg h, ENNReal.ofReal_zero]
  obtain ⟨hsum, hle⟩ := hQ.2 w hwE
  have hind : f = fun z => (1 / rate Q w) *
      E.indicator (fun y : ℤ => if y ≠ w then Q w y else 0) z := by
    funext z; simp only [hf, Set.indicator]
    by_cases h1 : z ∈ E <;> by_cases h2 : z ≠ w <;> simp [h1, h2, div_eq_inv_mul]
  have hsumf : Summable f := by
    rw [hind]
    exact ((summable_subtype_iff_indicator (f := fun y : ℤ => if y ≠ w then Q w y else 0)).mp
      hsum).mul_left _
  simp only [hjp]
  rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hsumf]
  apply ENNReal.ofReal_le_one.mpr
  rw [hind, tsum_mul_left, ← tsum_subtype E (fun y : ℤ => if y ≠ w then Q w y else 0)]
  unfold offDiagSum at hle
  rw [div_mul_eq_mul_div, one_mul, div_le_one hr]
  exact hle

lemma pathWeight_snoc (E : Set ℤ) (Q : ℤ → ℤ → ℝ) {n : ℕ} (ω : Fin (n + 1) → ℤ) (z : ℤ) :
    pathWeight E Q (Fin.snoc ω z : Fin (n + 2) → ℤ) =
      pathWeight E Q ω * jumpProb E Q (ω (Fin.last n)) z := by
  unfold pathWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun k _ => ?_
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · simp only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]

lemma jumpTime_snoc (Q : ℤ → ℤ → ℝ) {n : ℕ} (ω : Fin (n + 1) → ℤ) (z : ℤ)
    (e : Fin (n + 2) → ℝ) :
    jumpTime Q (Fin.snoc ω z : Fin (n + 2) → ℤ) e =
      jumpTime Q ω (Fin.init e) + holdTime Q ω (Fin.init e) (Fin.last n) := by
  unfold jumpTime holdTime
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.init]

end TransLe1

open SkipFreeFluct.MBI TransLe1 in
theorem solution (E : Set ℤ) (Q : ℤ → ℤ → ℝ) (hQ : IsQMatrix E Q) (t : ℝ)
    (x : ℤ) : ∑' y : ℤ, transition E Q t x y ≤ 1 := by
  classical
  set T := ENNReal.ofReal t with hTdef
  set F : ℕ → ℝ≥0∞ := fun n => ∑' ω : Fin (n + 1) → ℤ,
    if ω 0 = x then pathWeight E Q ω * clockLaw n {e | jumpTime Q ω e ≤ T} else 0 with hF
  set G : ℕ → ℝ≥0∞ := fun n => ∑' ω : Fin (n + 1) → ℤ,
    if ω 0 = x then pathWeight E Q ω * clockLaw n {e | jumpTime Q ω e ≤ T ∧
      T < jumpTime Q ω e + holdTime Q ω e (Fin.last n)} else 0 with hG
  have hstep : ∀ n, G n + F (n + 1) ≤ F n := by
    intro n
    have hF1 : F (n + 1) ≤ ∑' ω : Fin (n + 1) → ℤ, if ω 0 = x then pathWeight E Q ω *
        clockLaw n {e | jumpTime Q ω e + holdTime Q ω e (Fin.last n) ≤ T} else 0 := by
      simp only [hF]
      rw [← (Fin.snocEquiv (fun _ => ℤ)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
      refine ENNReal.tsum_le_tsum fun ω => ?_
      have h0 : ∀ z, (Fin.snoc ω z : Fin (n + 2) → ℤ) 0 = ω 0 := fun z => by
        have : (0 : Fin (n + 2)) = Fin.castSucc (0 : Fin (n + 1)) := rfl
        rw [this, Fin.snoc_castSucc]
      have hK : ∀ z, clockLaw (n + 1) {e | jumpTime Q (Fin.snoc ω z : Fin (n + 2) → ℤ) e ≤ T} =
          clockLaw n {e | jumpTime Q ω e + holdTime Q ω e (Fin.last n) ≤ T} := fun z => by
        simp only [jumpTime_snoc]
        exact clockLaw_init n {e | jumpTime Q ω e + holdTime Q ω e (Fin.last n) ≤ T}
          (measurableSet_le ((measurable_jumpTime Q ω).add (measurable_holdTime Q ω _))
            measurable_const)
      have hs : ∀ a, (Fin.snocEquiv (fun _ => ℤ)) (a, ω) = (Fin.snoc ω a : Fin (n + 2) → ℤ) :=
        fun a => rfl
      simp only [hs, h0, hK, pathWeight_snoc]
      by_cases hx : ω 0 = x
      · simp only [hx, if_true]
        rw [show (fun z => pathWeight E Q ω * jumpProb E Q (ω (Fin.last n)) z *
            clockLaw n {e | jumpTime Q ω e + holdTime Q ω e (Fin.last n) ≤ T}) =
            fun z => (pathWeight E Q ω * clockLaw n
              {e | jumpTime Q ω e + holdTime Q ω e (Fin.last n) ≤ T}) *
              jumpProb E Q (ω (Fin.last n)) z from funext fun z => by ring]
        rw [ENNReal.tsum_mul_left]
        exact mul_le_of_le_one_right' (jumpProb_tsum_le_one E Q hQ _)
      · simp [hx]
    calc G n + F (n + 1) ≤ G n + ∑' ω : Fin (n + 1) → ℤ, (if ω 0 = x then pathWeight E Q ω *
          clockLaw n {e | jumpTime Q ω e + holdTime Q ω e (Fin.last n) ≤ T} else 0) :=
          add_le_add le_rfl hF1
      _ = F n := by
        simp only [hG, hF]
        rw [← ENNReal.tsum_add]
        congr 1; funext ω
        split_ifs
        · rw [← mul_add, split_event]
        · simp
  have hF0 : F 0 ≤ 1 := by
    simp only [hF]
    calc (∑' ω : Fin 1 → ℤ, if ω 0 = x then pathWeight E Q ω *
          clockLaw 0 {e | jumpTime Q ω e ≤ T} else 0)
        ≤ ∑' ω : Fin 1 → ℤ, if ω 0 = x then (1 : ℝ≥0∞) else 0 := by
          refine ENNReal.tsum_le_tsum fun ω => ?_
          split_ifs
          · simp only [pathWeight, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
            exact prob_le_one
          · exact le_rfl
      _ = 1 := by
          rw [← (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq]
          simp
  have hGsum : ∑' n, G n ≤ 1 := by
    have hind : ∀ N, ∑ i ∈ Finset.range N, G i + F N ≤ F 0 := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, add_assoc]
        exact (add_le_add_right (hstep N) _).trans ih
    refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
    exact (le_self_add.trans (hind N)).trans hF0
  have hmain : ∑' y, transition E Q t x y ≤ ∑' n, G n := by
    calc ∑' y, transition E Q t x y
        ≤ ∑' y : ℤ, ∑' n : ℕ, ∑' ω : Fin (n + 1) → ℤ,
            (if ω 0 = x ∧ ω (Fin.last n) = y then pathWeight E Q ω * clockLaw n
              {e | jumpTime Q ω e ≤ T ∧ T < jumpTime Q ω e + holdTime Q ω e (Fin.last n)}
              else 0) := by
          refine ENNReal.tsum_le_tsum fun y => ?_
          unfold transition
          split_ifs
          · exact le_rfl
          · positivity
      _ = ∑' n, G n := by
          rw [ENNReal.tsum_comm]
          congr 1; funext n
          rw [ENNReal.tsum_comm]
          simp only [hG]
          congr 1; funext ω
          by_cases hx : ω 0 = x
          · simp [hx]
          · simp [hx]
  exact hmain.trans hGsum
