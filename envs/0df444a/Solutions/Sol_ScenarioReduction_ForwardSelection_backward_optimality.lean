-- Prove2me | solution 1 for ScenarioReduction.ForwardSelection.backward_optimality
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:19:47.616478+00:00
-- url     : https://prove2.me/submissions/a25799c8-2666-4506-9464-798e35c6cdee

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


private theorem selected_injective {N : ℕ} (c : Fin N → Fin N → ℝ) (p : Fin N → ℝ)
    (hN : 1 < N) (m : ℕ) (l : ℕ → Fin N) (hl : IsBackwardGreedy c p hN m l) :
    Set.InjOn l (Icc 1 m) := by
  intro i hi j hj he
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · apply (hl j hj).1
    exact mem_image.mpr ⟨i,mem_Ico.mpr ⟨(mem_Icc.mp hi).1,hij⟩,he⟩
  · apply (hl i hi).1
    exact mem_image.mpr ⟨j,mem_Ico.mpr ⟨(mem_Icc.mp hj).1,hji⟩,he.symm⟩

private theorem inf_eq_at {N : ℕ} (d : Fin N → ℝ) (S : Finset (Fin N))
    (hS : S.Nonempty) (j : Fin N) (hj : j ∈ S) (hmin : ∀ k ∈ S, d j ≤ d k) :
    S.inf' hS d = d j := le_antisymm (Finset.inf'_le d hj) (Finset.le_inf' hS d hmin)

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (h : ℝ → ℝ) (hh : IsGrowthFunction h) (ω₀ : E)
    (ω : Fin N → E) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hN : 1 < N) (n : ℕ) (hn1 : 1 ≤ n) (hnN : n < N) (l : ℕ → Fin N)
    (hl : IsBackwardGreedy (scenCost h ω₀ ω) p hN (N - n) l)
    (hcond : ∀ i ∈ Finset.Icc 1 (N - n), ∃ j : Fin N, j ≠ l i ∧
      (∀ j' : Fin N, j' ≠ l i → scenCost h ω₀ ω (l i) j ≤ scenCost h ω₀ ω (l i) j') ∧
      j ∉ ((Finset.Icc 1 (N - n)).erase i).image l) :
    ∃ hL : ((Finset.Icc 1 (N - n)).image l)ᶜ.Nonempty,
      ((Finset.Icc 1 (N - n)).image l).card = N - n ∧
      IsLeast {x : ℝ | ∃ J : Finset (Fin N), ∃ hJ : Jᶜ.Nonempty, J.card = N - n ∧
          x = reductionCost (scenCost h ω₀ ω) p J hJ}
        (reductionCost (scenCost h ω₀ ω) p ((Finset.Icc 1 (N - n)).image l) hL) := by
  have hinj := selected_injective _ p hN (N-n) l hl
  have hcard : ((Icc 1 (N-n)).image l).card = N-n := by
    rw [card_image_of_injOn hinj]
    simp
  have hL : ((Icc 1 (N-n)).image l)ᶜ.Nonempty := by
    apply card_pos.mp
    rw [card_compl,Fintype.card_fin,hcard]
    omega
  have heq : reductionCost (scenCost h ω₀ ω) p ((Icc 1 (N-n)).image l) hL =
      ∑ i ∈ Icc 1 (N-n), singleCost (scenCost h ω₀ ω) p hN (l i) := by
    unfold reductionCost
    rw [sum_image hinj]
    apply sum_congr rfl
    intro i hi
    obtain ⟨j,hji,hmin,hjout⟩ := hcond i hi
    have hj : j ∉ (Icc 1 (N-n)).image l := by
      intro hmem
      obtain ⟨k,hk,hkj⟩ := mem_image.mp hmem
      by_cases hki : k=i
      · exact hji (hki ▸ hkj.symm)
      · exact hjout (mem_image.mpr ⟨k,mem_erase.mpr ⟨hki,hk⟩,hkj⟩)
    have hlocal := inf_eq_at (fun k => scenCost h ω₀ ω (l i) k) _ hL j (mem_compl.mpr hj)
      (fun k hk => hmin k (fun hki => (mem_compl.mp hk) (hki ▸ mem_image.mpr ⟨i,hi,rfl⟩)))
    have hglobal := inf_eq_at (fun k => scenCost h ω₀ ω (l i) k) _ (univ_erase_nonempty hN (l i)) j
      (mem_erase.mpr ⟨hji,mem_univ _⟩) (fun k hk => hmin k (mem_erase.mp hk).1)
    unfold singleCost
    rw [hlocal,hglobal]
  refine ⟨hL,hcard,⟨?_,?_⟩⟩
  · exact ⟨(Icc 1 (N-n)).image l,hL,hcard,rfl⟩
  · rintro y ⟨J,hJ,hJcard,rfl⟩
    rw [heq]
    exact lower_bound _ p (fun i => (hp i).le) hN (N-n) l hl J hJ hJcard
