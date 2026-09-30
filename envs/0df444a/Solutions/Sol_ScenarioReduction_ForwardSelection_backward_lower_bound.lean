-- Prove2me | solution 1 for ScenarioReduction.ForwardSelection.backward_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:18:51.401998+00:00
-- url     : https://prove2.me/submissions/fcc0298d-7eb1-4fa5-8dbc-1727abacdd9f

import Definitions.Def_ScenarioReduction_ForwardSelection_fmCost
import Definitions.Def_ScenarioReduction_ForwardSelection_reductionCost
import Definitions.Def_ScenarioReduction_ForwardSelection_IsBackwardGreedy
import Mathlib.Tactic
set_option autoImplicit false
open ScenarioReduction.ForwardSelection Finset

private theorem greedy_sum {N : ℕ} (d : Fin N → ℝ) (l : ℕ → Fin N) (m : ℕ)
    (hl : ∀ i ∈ Icc 1 m, ∀ j, j ∉ (Ico 1 i).image l → d (l i) ≤ d j)
    (J : Finset (Fin N)) (hcard : J.card=m) : ∑ i ∈ Icc 1 m, d (l i) ≤ ∑ j ∈ J, d j := by
  induction m generalizing J with
  | zero =>
    have he : J=∅ := card_eq_zero.mp hcard
    simp [he]
  | succ m ih =>
    have hs : ((Ico 1 (m+1)).image l).card ≤ m := by
      calc _ ≤ (Ico 1 (m+1)).card := card_image_le
           _ = m := by simp
    obtain ⟨a,ha,hna⟩ := exists_mem_notMem_of_card_lt_card (show ((Ico 1 (m+1)).image l).card < J.card by omega)
    have hprev := ih (fun i hi => hl i (mem_Icc.mpr ⟨(mem_Icc.mp hi).1,le_trans (mem_Icc.mp hi).2 (Nat.le_succ m)⟩))
      (J.erase a) (by rw [card_erase_of_mem ha,hcard]; omega)
    have hmin := hl (m+1) (by simp) a hna
    have hj := sum_erase_add (s := J) (f := d) ha
    have hI : Icc 1 (m+1) = insert (m+1) (Icc 1 m) := by
      ext j
      simp only [mem_Icc,mem_insert]
      omega
    rw [hI,sum_insert (by simp)]
    linarith

private theorem single_le_reduction {N : ℕ} (c : Fin N → Fin N → ℝ) (p : Fin N → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hN : 1 < N) (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) :
    ∑ i ∈ J, singleCost c p hN i ≤ reductionCost c p J hJ := by
  unfold reductionCost
  apply sum_le_sum
  intro i hi
  unfold singleCost
  apply mul_le_mul_of_nonneg_left _ (hp i)
  apply Finset.le_inf'
  intro j hj
  apply Finset.inf'_le
  exact mem_erase.mpr ⟨fun heq => (mem_compl.mp hj) (heq ▸ hi),mem_univ _⟩

private theorem lower_bound {N : ℕ} (c : Fin N → Fin N → ℝ) (p : Fin N → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hN : 1 < N) (m : ℕ) (l : ℕ → Fin N)
    (hl : IsBackwardGreedy c p hN m l) (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) (hcard : J.card=m) :
    ∑ i ∈ Icc 1 m, singleCost c p hN (l i) ≤ reductionCost c p J hJ :=
  (greedy_sum _ l m (fun i hi => (hl i hi).2) J hcard).trans (single_le_reduction c p hp hN J hJ)

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (h : ℝ → ℝ) (hh : IsGrowthFunction h) (ω₀ : E)
    (ω : Fin N → E) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hN : 1 < N) (n : ℕ) (hn1 : 1 ≤ n) (hnN : n < N) (l : ℕ → Fin N)
    (hl : IsBackwardGreedy (scenCost h ω₀ ω) p hN (N - n) l)
    (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) (hcard : J.card = N - n) :
    ∑ i ∈ Finset.Icc 1 (N - n), singleCost (scenCost h ω₀ ω) p hN (l i) ≤
      reductionCost (scenCost h ω₀ ω) p J hJ :=
  lower_bound _ p (fun i => (hp i).le) hN (N-n) l hl J hJ hcard
