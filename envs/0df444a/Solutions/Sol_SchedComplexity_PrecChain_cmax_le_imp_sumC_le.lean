-- Prove2me | solution 1 for SchedComplexity.PrecChain.cmax_le_imp_sumC_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:36:43.024861+00:00
-- url     : https://prove2.me/submissions/e5e29ebb-fe11-4509-8c80-b32a8d8ced9f

import Mathlib
import Definitions.Def_SchedComplexity_PrecChain_Model
import Definitions.Def_SchedComplexity_PrecChain_Construction



namespace SchedComplexity.PrecChain

theorem pc_sum1 (y N : ℕ) :
    ∑ i ∈ Finset.range N, (((y + i + 1 : ℕ)) : ℚ) = (N : ℚ) * y + (N : ℚ) * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem pc_sum2 (y N : ℕ) :
    ∑ i ∈ Finset.range N, (((y + i + 2 : ℕ)) : ℚ) = (N : ℚ) * y + (N : ℚ) * (N + 1) / 2 + N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem pc_thr (n y : ℕ) : chainThresholdQ n y =
    ((n : ℚ) + (nNew n y : ℚ)) * y + (nNew n y : ℚ) * ((nNew n y : ℚ) + 1) / 2 := by
  unfold chainThresholdQ; push_cast; ring

theorem pc_le_core (pstar : ℕ) (I : Instance) (hI : I.InClass pstar) (y' : ℕ)
    (hy' : y' ≤ I.n * pstar) (h : CmaxYes I y') :
    ∃ σ : Schedule (chainExtend I y'), σ.IsFeasible ∧
      (σ.totalCompletion : ℚ) ≤ chainThresholdQ I.n y' := by
  obtain ⟨hm, hp, hA⟩ := hI
  obtain ⟨σ0, ⟨hf1, hf2⟩, hc⟩ := h
  let E := chainExtend I y'
  have hEn : E.n = I.n + nNew I.n y' := rfl
  have hEp : ∀ j : Fin E.n, E.p j = if h : (j : ℕ) < I.n then I.p ⟨j, h⟩ else 1 := fun j => rfl
  let σ : Schedule E :=
    { machine := fun j => if h : (j : ℕ) < I.n then σ0.machine ⟨j, h⟩ else ⟨0, hm⟩
      start := fun j => if h : (j : ℕ) < I.n then σ0.start ⟨j, h⟩ else y' + ((j : ℕ) - I.n) }
  have hcomp_lt : ∀ j : Fin E.n, ∀ h : (j : ℕ) < I.n, σ.completion j = σ0.completion ⟨j, h⟩ := by
    intro j h
    simp [Schedule.completion, σ, hEp, h, Schedule.completion]
  have hcomp_ge : ∀ j : Fin E.n, ¬ (j : ℕ) < I.n → σ.completion j = y' + ((j : ℕ) - I.n) + 1 := by
    intro j h
    simp [Schedule.completion, σ, hEp, h]
  have hstart_lt : ∀ j : Fin E.n, ∀ h : (j : ℕ) < I.n, σ.start j = σ0.start ⟨j, h⟩ := by
    intro j h; simp [σ, h]
  have hstart_ge : ∀ j : Fin E.n, ¬ (j : ℕ) < I.n → σ.start j = y' + ((j : ℕ) - I.n) := by
    intro j h; simp [σ, h]
  refine ⟨σ, ⟨?_, ?_⟩, ?_⟩
  · intro j k hjk hmach
    by_cases hj : (j : ℕ) < I.n <;> by_cases hk : (k : ℕ) < I.n
    · have hm' : σ0.machine ⟨j, hj⟩ = σ0.machine ⟨k, hk⟩ := by
        have e1 : σ.machine j = σ0.machine ⟨j, hj⟩ := dif_pos hj
        have e2 : σ.machine k = σ0.machine ⟨k, hk⟩ := dif_pos hk
        rw [e1, e2] at hmach; exact hmach
      have hne : (⟨j, hj⟩ : Fin I.n) ≠ ⟨k, hk⟩ := fun e => hjk (Fin.ext (by simpa using congrArg Fin.val e))
      rcases hf1 _ _ hne hm' with h1 | h1
      · left; rw [hcomp_lt j hj, hstart_lt k hk]; exact h1
      · right; rw [hcomp_lt k hk, hstart_lt j hj]; exact h1
    · left; rw [hcomp_lt j hj, hstart_ge k hk]; have := hc ⟨j, hj⟩; omega
    · right; rw [hcomp_lt k hk, hstart_ge j hj]; have := hc ⟨k, hk⟩; omega
    · have hne : (j : ℕ) ≠ k := fun e => hjk (Fin.ext e)
      rcases lt_or_gt_of_ne hne with h1 | h1
      · left; rw [hcomp_ge j hj, hstart_ge k hk]; omega
      · right; rw [hcomp_ge k hk, hstart_ge j hj]; omega
  · intro j k hjk
    have hjk' : (if hk : (k : ℕ) < I.n then
      (if hj : (j : ℕ) < I.n then I.prec ⟨j, hj⟩ ⟨k, hk⟩ else false)
      else decide ((j : ℕ) < k)) = true := hjk
    by_cases hk : (k : ℕ) < I.n
    · rw [dif_pos hk] at hjk'
      by_cases hj : (j : ℕ) < I.n
      · rw [dif_pos hj] at hjk'
        rw [hcomp_lt j hj, hstart_lt k hk]; exact hf2 _ _ hjk'
      · rw [dif_neg hj] at hjk'; exact absurd hjk' (by simp)
    · rw [dif_neg hk] at hjk'
      have hjk2 : (j : ℕ) < k := by simpa using hjk'
      by_cases hj : (j : ℕ) < I.n
      · rw [hcomp_lt j hj, hstart_ge k hk]; have := hc ⟨j, hj⟩; omega
      · rw [hcomp_ge j hj, hstart_ge k hk]; omega
  · -- total
    have hs : σ.totalCompletion = ∑ i : Fin I.n, σ.completion (Fin.castAdd (nNew I.n y') i) +
        ∑ i : Fin (nNew I.n y'), σ.completion (Fin.natAdd I.n i) :=
      Fin.sum_univ_add (a := I.n) (b := nNew I.n y') (fun j => σ.completion j)
    rw [hs]
    have h1 : ∑ i : Fin I.n, σ.completion (Fin.castAdd (nNew I.n y') i) ≤ I.n * y' := by
      calc _ ≤ ∑ i : Fin I.n, y' := by
            apply Finset.sum_le_sum; intro i _
            exact (hcomp_lt (Fin.castAdd (nNew I.n y') i) (by simp)).trans_le (hc _)
        _ = _ := by simp
    have h2 : ∑ i : Fin (nNew I.n y'), σ.completion (Fin.natAdd I.n i) =
        ∑ i ∈ Finset.range (nNew I.n y'), (y' + i + 1) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => y' + i + 1)]
      apply Finset.sum_congr rfl; intro i _
      exact (hcomp_ge (Fin.natAdd I.n i) (by simp)).trans (by simp)
    rw [h2]
    push_cast
    rw [pc_thr]
    have h1' : ((∑ i : Fin I.n, σ.completion (Fin.castAdd (nNew I.n y') i) : ℕ) : ℚ) ≤ (I.n : ℚ) * y' := by
      exact_mod_cast h1
    have := pc_sum1 y' (nNew I.n y')
    push_cast at h1' this ⊢
    linarith

end SchedComplexity.PrecChain

open SchedComplexity.PrecChain


theorem solution (pstar : ℕ) (I : Instance) (hI : I.InClass pstar) (y' : ℕ)
    (hy' : y' ≤ I.n * pstar) (h : CmaxYes I y') :
    ∃ σ : Schedule (chainExtend I y'), σ.IsFeasible ∧
      (σ.totalCompletion : ℚ) ≤ chainThresholdQ I.n y' := by
  exact pc_le_core pstar I hI y' hy' h
