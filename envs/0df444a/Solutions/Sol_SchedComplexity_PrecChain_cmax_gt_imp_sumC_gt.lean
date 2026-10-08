-- Prove2me | solution 1 for SchedComplexity.PrecChain.cmax_gt_imp_sumC_gt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:38:09.258572+00:00
-- url     : https://prove2.me/submissions/649e1734-543f-4d2a-9cfa-fa25bf6a45d7

import Mathlib
import Definitions.Def_SchedComplexity_PrecChain_Model
import Definitions.Def_SchedComplexity_PrecChain_Construction



namespace SchedComplexity.PrecChain

theorem pc3_sum2 (y N : ℕ) :
    ∑ i ∈ Finset.range N, (((y + i + 2 : ℕ)) : ℚ) = (N : ℚ) * y + (N : ℚ) * (N + 1) / 2 + N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem pc3_gt_core (pstar : ℕ) (I : Instance) (hI : I.InClass pstar) (y' : ℕ)
    (hy' : y' ≤ I.n * pstar) (h : ¬ CmaxYes I y') :
    ∀ τ : Schedule (chainExtend I y'), τ.IsFeasible →
      chainThresholdQ I.n y' < (τ.totalCompletion : ℚ) := by
  obtain ⟨hm, hp, hA⟩ := hI
  intro τ ⟨hf1, hf2⟩
  -- restriction
  have hEp : ∀ j : Fin (chainExtend I y').n, (chainExtend I y').p j =
      if h : (j : ℕ) < I.n then I.p ⟨j, h⟩ else 1 := fun j => rfl
  have hlift : ∀ j : Fin I.n, (j : ℕ) < I.n + nNew I.n y' := fun j => by
    have := j.2; omega
  have hnE : (chainExtend I y').n = I.n + nNew I.n y' := rfl
  let emb : Fin I.n → Fin (chainExtend I y').n := fun j => ⟨j, hlift j⟩
  have hcompE : ∀ j : Fin I.n, τ.completion (emb j) = τ.start (emb j) + I.p j := by
    intro j
    show τ.start (emb j) + (chainExtend I y').p (emb j) = _
    rw [hEp]; simp [emb, j.2]
  let τ0 : Schedule I := ⟨fun j => τ.machine (emb j), fun j => τ.start (emb j)⟩
  have hτ0 : ∀ j, τ0.completion j = τ.completion (emb j) := by
    intro j; rw [hcompE]; rfl
  have hfeas0 : τ0.IsFeasible := by
    constructor
    · intro j k hjk hmach
      have hne : emb j ≠ emb k := fun e => hjk (Fin.ext (by simpa [emb] using congrArg Fin.val e))
      rcases hf1 _ _ hne hmach with h1 | h1
      · left; rw [hτ0]; exact h1
      · right; rw [hτ0]; exact h1
    · intro j k hjk
      rw [hτ0]
      apply hf2
      show (if hk : ((emb k : Fin _) : ℕ) < I.n then
        (if hj : ((emb j : Fin _) : ℕ) < I.n then I.prec ⟨_, hj⟩ ⟨_, hk⟩ else false)
        else decide (((emb j : Fin _) : ℕ) < (emb k : Fin _))) = true
      simp only [emb, j.2, k.2, dif_pos]
      exact hjk
  -- a late original job
  have hlate : ∃ j0 : Fin I.n, y' < τ0.completion j0 := by
    by_contra hcon
    push_neg at hcon
    exact h ⟨τ0, hfeas0, hcon⟩
  obtain ⟨j0, hj0⟩ := hlate
  have hn : 1 ≤ I.n := by have := j0.2; omega
  obtain ⟨a, ha⟩ : ∃ a, I.n = a + 1 := ⟨I.n - 1, by omega⟩
  have hnn : nNew I.n y' = a * y' := by simp [nNew, ha]
  -- chain of new jobs
  have hchain : ∀ i : ℕ, ∀ hi : i < nNew I.n y',
      y' + i + 2 ≤ τ.completion ⟨I.n + i, by rw [hnE]; omega⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi
      have hpre : (chainExtend I y').Precedes (emb j0) ⟨I.n + 0, by rw [hnE]; omega⟩ := by
        show (if hk : I.n + 0 < I.n then _ else decide (((emb j0 : Fin _) : ℕ) < I.n + 0)) = true
        rw [dif_neg (by omega)]
        simp [emb, j0.2]
      have h1 := hf2 _ _ hpre
      have h2 : τ.completion ⟨I.n + 0, by rw [hnE]; omega⟩ = τ.start ⟨I.n + 0, by rw [hnE]; omega⟩ + 1 := by
        show τ.start _ + (chainExtend I y').p _ = _
        rw [hEp]; simp
      have h3 := hj0; rw [hτ0] at h3
      omega
    | succ i ih =>
      intro hi
      have hpre : (chainExtend I y').Precedes ⟨I.n + i, by rw [hnE]; omega⟩ ⟨I.n + (i + 1), by rw [hnE]; omega⟩ := by
        show (if hk : I.n + (i+1) < I.n then _ else decide (I.n + i < I.n + (i + 1))) = true
        rw [dif_neg (by omega)]
        simp
      have h1 := hf2 _ _ hpre
      have h2 : τ.completion ⟨I.n + (i+1), by rw [hnE]; omega⟩ = τ.start ⟨I.n + (i+1), by rw [hnE]; omega⟩ + 1 := by
        show τ.start _ + (chainExtend I y').p _ = _
        rw [hEp]; simp
      have h3 := ih (by omega)
      omega
  -- sums
  have hs : τ.totalCompletion = ∑ i : Fin I.n, τ.completion (Fin.castAdd (nNew I.n y') i) +
        ∑ i : Fin (nNew I.n y'), τ.completion (Fin.natAdd I.n i) :=
    Fin.sum_univ_add (a := I.n) (b := nNew I.n y') (fun j => τ.completion j)
  have h1 : I.n + y' ≤ ∑ i : Fin I.n, τ.completion (Fin.castAdd (nNew I.n y') i) := by
    have hge : ∀ i : Fin I.n, 1 + (if i = j0 then y' else 0) ≤
        τ.completion (Fin.castAdd (nNew I.n y') i) := by
      intro i
      have e : τ.completion (Fin.castAdd (nNew I.n y') i) = τ.completion (emb i) := rfl
      rw [e, ← hτ0, Schedule.completion]
      have := (hp i).1
      by_cases hi : i = j0
      · subst hi; rw [if_pos rfl]; have := hj0; rw [Schedule.completion] at this; omega
      · rw [if_neg hi]; omega
    calc I.n + y' = ∑ i : Fin I.n, (1 + (if i = j0 then y' else 0)) := by
          rw [Finset.sum_add_distrib]; simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hge i)
  have h2 : ∑ i ∈ Finset.range (nNew I.n y'), (y' + i + 2) ≤
      ∑ i : Fin (nNew I.n y'), τ.completion (Fin.natAdd I.n i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => y' + i + 2)]
    apply Finset.sum_le_sum; intro i _
    exact hchain i i.2
  rw [hs]
  have h1q : ((I.n + y' : ℕ) : ℚ) ≤ ((∑ i : Fin I.n, τ.completion (Fin.castAdd (nNew I.n y') i) : ℕ) : ℚ) := by
    exact_mod_cast h1
  have h2q : ((∑ i ∈ Finset.range (nNew I.n y'), (y' + i + 2) : ℕ) : ℚ) ≤
      ((∑ i : Fin (nNew I.n y'), τ.completion (Fin.natAdd I.n i) : ℕ) : ℚ) := by
    exact_mod_cast h2
  have hq := pc3_sum2 y' (nNew I.n y')
  push_cast at h1q h2q hq ⊢
  unfold chainThresholdQ
  have hnq : (nNew I.n y' : ℚ) = (a : ℚ) * y' := by rw [hnn]; push_cast; ring
  have han : (I.n : ℚ) = a + 1 := by rw [ha]; push_cast; ring
  push_cast
  rw [han] at h1q ⊢
  nlinarith

end SchedComplexity.PrecChain

open SchedComplexity.PrecChain


theorem solution (pstar : ℕ) (I : Instance) (hI : I.InClass pstar) (y' : ℕ)
    (hy' : y' ≤ I.n * pstar) (h : ¬ CmaxYes I y') :
    ∀ σ : Schedule (chainExtend I y'), σ.IsFeasible →
      chainThresholdQ I.n y' < (σ.totalCompletion : ℚ) := by
  exact pc3_gt_core pstar I hI y' hy' h
