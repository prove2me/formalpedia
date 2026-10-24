-- Prove2me | solution 1 for SubsampleSubmod.SampleGreedy.display_4_1_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:45:45.111867+00:00
-- url     : https://prove2.me/submissions/b894579f-0de9-4718-a0fd-fe68e658eb57

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis
import Theorems.Thm_SubsampleSubmod_SampleGreedy_lemma_6
import Theorems.Thm_SubsampleSubmod_SampleGreedy_lemma_7
import Theorems.Thm_SubsampleSubmod_SampleGreedy_lemma_8

open SubsampleSubmod.SampleGreedy

/-- The display of §4.1.1 (p. 14). With `q = 1/(p+1)`, for Algorithm 2 run from an independent `T`
(OPT), non-negative submodular `f` and a `p`-extendible system:
`E[f(S)] ≥ E[f(S ∪ T)] − ∑_u E[|O_u \ S| · f(u | S_u)]
  ≥ E[f(S ∪ T)] − p/(p+1) ∑_u E[X_u · f(u | S_u)] ≥ E[f(S ∪ T)] − p · E[f(S)]`. -/
theorem solution {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hp : 1 ≤ p) (hf0 : ∀ S, 0 ≤ f S)
    (hsub : NonmonotoneSubmod.Shared.Submodular f) (hI : IsIndepSystem I)
    (hext : IsPExtendible p I) (T : Finset α) (hT : I T) :
    E2 (1 / ((p : ℝ) + 1)) f I T (fun st => f (st.S ∪ T)) -
        ∑ u : α, E2 (1 / ((p : ℝ) + 1)) f I T
          (fun st => ((st.Ou u \ st.S).card : ℝ) * marg f u (st.Su u)) ≤
      E2 (1 / ((p : ℝ) + 1)) f I T (fun st => f st.S) ∧
    E2 (1 / ((p : ℝ) + 1)) f I T (fun st => f (st.S ∪ T)) -
        ((p : ℝ) / ((p : ℝ) + 1)) * ∑ u : α, E2 (1 / ((p : ℝ) + 1)) f I T
          (fun st => (if u ∈ st.considered then (1 : ℝ) else 0) * marg f u (st.Su u)) ≤
      E2 (1 / ((p : ℝ) + 1)) f I T (fun st => f (st.S ∪ T)) -
        ∑ u : α, E2 (1 / ((p : ℝ) + 1)) f I T
          (fun st => ((st.Ou u \ st.S).card : ℝ) * marg f u (st.Su u)) ∧
    E2 (1 / ((p : ℝ) + 1)) f I T (fun st => f (st.S ∪ T)) -
        (p : ℝ) * E2 (1 / ((p : ℝ) + 1)) f I T (fun st => f st.S) ≤
      E2 (1 / ((p : ℝ) + 1)) f I T (fun st => f (st.S ∪ T)) -
        ((p : ℝ) / ((p : ℝ) + 1)) * ∑ u : α, E2 (1 / ((p : ℝ) + 1)) f I T
          (fun st => (if u ∈ st.considered then (1 : ℝ) else 0) * marg f u (st.Su u)) := by
  classical
  let q : ℝ := 1 / ((p : ℝ) + 1)
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    apply (div_le_one (by positivity : (0 : ℝ) < (p : ℝ) + 1)).mpr
    linarith
  have hfirst :
      E2 q f I T (fun st => f (st.S ∪ T)) -
          ∑ u : α, E2 q f I T
            (fun st => ((st.Ou u \ st.S).card : ℝ) * marg f u (st.Su u)) ≤
        E2 q f I T (fun st => f st.S) := by
    have hweighted :
        E2 q f I T (fun st => f (st.S ∪ T) -
          ∑ u : α, ((st.Ou u \ st.S).card : ℝ) * marg f u (st.Su u)) ≤
          E2 q f I T (fun st => f st.S) := by
      unfold E2
      apply Finset.sum_le_sum
      intro B _
      have hw : 0 ≤ sampleWeight q B :=
        mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (sub_nonneg.mpr hq1) _)
      exact mul_le_mul_of_nonneg_left (lemma_6 f I hsub hI T hT B) hw
    have hexpand :
        E2 q f I T (fun st => f (st.S ∪ T) -
          ∑ u : α, ((st.Ou u \ st.S).card : ℝ) * marg f u (st.Su u)) =
        E2 q f I T (fun st => f (st.S ∪ T)) -
          ∑ u : α, E2 q f I T
            (fun st => ((st.Ou u \ st.S).card : ℝ) * marg f u (st.Su u)) := by
      unfold E2
      simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
    rw [hexpand] at hweighted
    exact hweighted
  have hsecond :
      (∑ u : α, E2 q f I T
        (fun st => ((st.Ou u \ st.S).card : ℝ) * marg f u (st.Su u))) ≤
      ((p : ℝ) / ((p : ℝ) + 1)) * ∑ u : α, E2 q f I T
        (fun st => (if u ∈ st.considered then (1 : ℝ) else 0) * marg f u (st.Su u)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun u _ => lemma_7 f I p hp hI hext T hT u)
  have hthird :
      ((p : ℝ) / ((p : ℝ) + 1)) * ∑ u : α, E2 q f I T
        (fun st => (if u ∈ st.considered then (1 : ℝ) else 0) * marg f u (st.Su u)) ≤
      (p : ℝ) * E2 q f I T (fun st => f st.S) := by
    calc
      _ = (p : ℝ) * (q * ∑ u : α, E2 q f I T
          (fun st => (if u ∈ st.considered then (1 : ℝ) else 0) * marg f u (st.Su u))) := by
        dsimp [q]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (lemma_8 f I hf0 q hq0 hq1 T) hp0
  dsimp [q] at hfirst hsecond hthird
  exact ⟨hfirst, sub_le_sub_left hsecond _, sub_le_sub_left hthird _⟩
