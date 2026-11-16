-- Prove2me | solution 1 for PrivBayesTest.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-15T17:51:01.040504+00:00
-- url     : https://prove2.me/submissions/9578f8bd-0407-49dc-a0aa-843b1bd64bea

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
open MeasureTheory

namespace PrivateGroup
open Classical
variable {D O : Type*} [MeasurableSpace O] {n : ℕ}

lemma update_bound (A : (Fin n → D) → Measure O) (ε : ℝ) (hε : 0 ≤ ε)
    (hA : PrivLearn.Generic.IsDP A ε) (z : Fin n → D) (i : Fin n) (v : D)
    (S : Set O) (hS : MeasurableSet S) :
    A z S ≤ ENNReal.ofReal (Real.exp ε) * A (Function.update z i v) S := by
  by_cases hi : z i = v
  · have he : Function.update z i v = z := by rw [← hi, Function.update_eq_self]
    rw [he]
    calc
      A z S = 1 * A z S := (one_mul _).symm
      _ ≤ ENNReal.ofReal (Real.exp ε) * A z S := by
        gcongr
        simpa using ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr hε)
  · apply hA z (Function.update z i v)
    · refine ⟨i, ?_, ?_⟩
      · simpa using hi
      · intro j hj
        simp [Function.update_of_ne hj]
    · exact hS

lemma finset_bound (A : (Fin n → D) → Measure O) (ε : ℝ) (hε : 0 ≤ ε)
    (hA : PrivLearn.Generic.IsDP A ε) (s : Finset (Fin n)) (z z' : Fin n → D)
    (hs : ∀ i ∉ s, z i = z' i) (S : Set O) (hS : MeasurableSet S) :
    A z S ≤ ENNReal.ofReal (Real.exp ((s.card : ℝ) * ε)) * A z' S := by
  induction s using Finset.induction_on generalizing z with
  | empty =>
    have hz : z = z' := funext fun i => hs i (by simp)
    simp [hz]
  | @insert i s hi ih =>
    have hu : ∀ j ∉ s, Function.update z i (z' i) j = z' j := by
      intro j hj
      by_cases hji : j = i
      · subst j; simp
      · rw [Function.update_of_ne hji]
        exact hs j (by simp [hj,hji])
    calc
      A z S ≤ ENNReal.ofReal (Real.exp ε) * A (Function.update z i (z' i)) S :=
        update_bound A ε hε hA z i (z' i) S hS
      _ ≤ ENNReal.ofReal (Real.exp ε) *
          (ENNReal.ofReal (Real.exp ((s.card : ℝ) * ε)) * A z' S) :=
        by gcongr; exact ih _ hu
      _ = ENNReal.ofReal (Real.exp (((insert i s).card : ℝ) * ε)) * A z' S := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        congr 3
        rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
        ring

lemma event_bound (A : (Fin n → D) → Measure O) (ε : ℝ) (hε : 0 ≤ ε)
    (hA : PrivLearn.Generic.IsDP A ε) (k : ℕ) (z z' : Fin n → D)
    (hk : {i : Fin n | z i ≠ z' i}.ncard ≤ k) (S : Set O) (hS : MeasurableSet S) :
    A z S ≤ ENNReal.ofReal (Real.exp (k * ε)) * A z' S := by
  let s : Finset (Fin n) := Finset.univ.filter fun i => z i ≠ z' i
  have hs : ∀ i ∉ s, z i = z' i := by simp [s]
  have hc : s.card ≤ k := by
    have he : {i : Fin n | z i ≠ z' i} = (s : Set (Fin n)) := by ext; simp [s]
    simpa [he] using hk
  apply (finset_bound A ε hε hA s z z' hs S hS).trans
  gcongr

end PrivateGroup

theorem solution {D O : Type*} [MeasurableSpace O] {n : ℕ}
    (A : (Fin n → D) → Measure O) [∀ z, IsFiniteMeasure (A z)]
    (ε : ℝ) (hε : 0 < ε) (hA : PrivLearn.Generic.IsDP A ε) (k : ℕ)
    (z z' : Fin n → D) (hk : {i : Fin n | z i ≠ z' i}.ncard ≤ k) :
    (∀ S : Set O, MeasurableSet S → A z S ≤ ENNReal.ofReal (Real.exp (k * ε)) * A z' S) ∧
      A z ≪ A z' ∧
      ∀ᵐ y ∂(A z'), (A z).rnDeriv (A z') y ≤ ENNReal.ofReal (Real.exp (k * ε)) := by
  have he := PrivateGroup.event_bound A ε hε.le hA k z z' hk
  have hm : A z ≤ ENNReal.ofReal (Real.exp (k * ε)) • A z' := by
    apply Measure.le_iff.mpr
    intro S hS
    simpa using he S hS
  refine ⟨he, ?_, ?_⟩
  · intro S hS
    have hh := hm S
    simpa [hS] using hh
  · apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (A z |>.measurable_rnDeriv (A z'))
    intro S hS hfin
    calc
      ∫⁻ y in S, (A z).rnDeriv (A z') y ∂(A z') ≤ A z S :=
        Measure.setLIntegral_rnDeriv_le S
      _ ≤ ENNReal.ofReal (Real.exp (k * ε)) * A z' S := he S hS
      _ = ∫⁻ _ in S, ENNReal.ofReal (Real.exp (k * ε)) ∂(A z') := by simp
