-- Prove2me | solution 1 for SluggishCapability.Myopic.ext_marginal_stationary
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:33:39.384998+00:00
-- url     : https://prove2.me/submissions/9add9ae2-7e0e-4b0b-808c-7beb2c803f5e

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting

open MarkovMixing

open SluggishCapability.Myopic in
theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (f : S → ℕ) (M : ℕ) (hP : IsStochastic P) (hM : ∀ s, f s ≤ M) :
    IsStochastic (extKernel P f M) ∧
    ∀ ν : Fin (M + 1) × S → ℝ, IsStationary (extKernel P f M) ν →
      IsStationary P (fun s => ∑ m : Fin (M + 1), ν (m, s)) := by
  have hstep : ∀ m d, m ≤ M → d ≤ M → myopicStep m d ≤ M := by
    intro m d hm hd
    unfold myopicStep
    split_ifs <;> omega
  have hcol : ∀ (m : Fin (M + 1)) (s' : S) (c : ℝ),
      ∑ m' : Fin (M + 1), (if (m' : ℕ) = myopicStep m (f s') then c else 0) = c := by
    intro m s' c
    have hj : myopicStep m (f s') < M + 1 :=
      Nat.lt_succ_of_le (hstep _ _ (Nat.lt_succ_iff.mp m.2) (hM s'))
    rw [Finset.sum_eq_single (⟨_, hj⟩ : Fin (M + 1))]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hrow : ∀ (x : Fin (M + 1) × S) (s' : S),
      ∑ m' : Fin (M + 1), extKernel P f M x (m', s') = P x.2 s' := by
    intro x s'
    unfold extKernel
    dsimp only
    convert hcol x.1 s' (P x.2 s')
  refine ⟨⟨fun x y => ?_, fun x => ?_⟩, ?_⟩
  · unfold extKernel
    split_ifs
    · exact hP.1 _ _
    · exact le_rfl
  · rw [Fintype.sum_prod_type_right]
    rw [Finset.sum_congr rfl fun s' _ => hrow x s']
    exact hP.2 x.2
  · rintro ν ⟨⟨hν0, hν1⟩, hνK⟩
    refine ⟨⟨fun s => Finset.sum_nonneg fun m _ => hν0 _, ?_⟩, ?_⟩
    · rw [← hν1, Fintype.sum_prod_type_right]
    · funext s'
      simp only [Matrix.vecMul, dotProduct]
      calc ∑ s, (∑ m, ν (m, s)) * P s s'
          = ∑ x : Fin (M + 1) × S, ν x * P x.2 s' := by
            rw [Fintype.sum_prod_type_right]
            simp only [Finset.sum_mul]
        _ = ∑ x : Fin (M + 1) × S, ν x * ∑ m' : Fin (M + 1), extKernel P f M x (m', s') := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [hrow]
        _ = ∑ m' : Fin (M + 1), ∑ x : Fin (M + 1) × S, ν x * extKernel P f M x (m', s') := by
            simp only [Finset.mul_sum]
            exact Finset.sum_comm
        _ = ∑ m', ν (m', s') := by
            refine Finset.sum_congr rfl fun m' _ => ?_
            exact congrFun hνK (m', s')
