-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.histories_normalization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:48:14.967217+00:00
-- url     : https://prove2.me/submissions/71264d9a-c818-4d12-bf16-7dc1c36d41fe

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P26

theorem g52b_rankOne_psd {I : Type*} [Fintype I] (v : I → ℂ) : (rankOne v).PosSemidef := by
  have : rankOne v = Matrix.vecMulVec v (star v) := by
    ext a b; simp [rankOne, Matrix.vecMulVec_apply]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star v

theorem g52b_sum_psd {I ι : Type*} [Fintype I] (s : Finset ι) (A : ι → Matrix I I ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih


/-- PDF p.21, question 2: Kraus histories form a measurement exactly when their total
satisfies all causal normalization constraints, not merely its final trace equation. -/
theorem solution (s : Signature) (n k q : ℕ)
    (hn : 0 < n) (hk : 0 < k) (K : Fin k → Fin q → Basis s n → ℂ) :
    CombInstrument s n k (fun i => ∑ a, rankOne (K i a)) ↔
      Normalized s n (∑ i, ∑ a, rankOne (K i a)) := by
  have hpsd : ∀ i, (∑ a, rankOne (K i a)).PosSemidef := fun i =>
    g52b_sum_psd _ _ fun a => g52b_rankOne_psd _
  constructor
  · rintro ⟨-, -, -, h⟩; exact h
  · intro h; exact ⟨hn, hk, hpsd, h⟩


end

