-- Prove2me | solution 1 for VeinottBaseStock.closed_chain_has_least
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:18:28.685982+00:00
-- url     : https://prove2.me/submissions/04b87085-8f57-484f-8b47-6ce6afef6831

import Mathlib

namespace VeinottBaseStock

theorem aux_ccl_mem {n : ℕ} (A : Set (Fin n → ℝ)) (hA : IsClosed A)
    (hchain : IsChain (· ≤ ·) A) (hne : A.Nonempty) (hbdd : BddBelow A) :
    sInf A ∈ A := by
  have : Nonempty A := hne.to_subtype
  have : IsDirected A (· ≥ ·) := ⟨fun a b => by
    by_cases h : a = b
    · exact ⟨a, le_refl _, h ▸ le_refl _⟩
    · have h' : (a : Fin n → ℝ) ≠ b := fun e => h (Subtype.ext e)
      rcases hchain a.2 b.2 h' with hab | hba
      · exact ⟨a, le_refl _, hab⟩
      · exact ⟨b, hba, le_refl _⟩⟩
  have hglb : IsGLB (Set.range (Subtype.val : A → Fin n → ℝ)) (sInf A) := by
    rw [Subtype.range_coe]
    exact isGLB_csInf hne hbdd
  have hmono : Monotone (Subtype.val : A → Fin n → ℝ) := fun a b h => h
  have ht := tendsto_atBot_isGLB hmono hglb
  exact hA.mem_of_tendsto ht (Filter.Eventually.of_forall fun x => x.2)

end VeinottBaseStock

open VeinottBaseStock

theorem solution {n : ℕ} (A : Set (Fin n → ℝ)) (hA : IsClosed A)
    (hchain : IsChain (· ≤ ·) A) (hne : A.Nonempty) (hbdd : BddBelow A) :
    ∃ a, IsLeast A a :=
  ⟨sInf A, aux_ccl_mem A hA hchain hne hbdd, (isGLB_csInf hne hbdd).1⟩
