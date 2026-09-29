-- Prove2me | solution 1 for RobustMDP.Discounted.lemma_two
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:01:36.070399+00:00
-- url     : https://prove2.me/submissions/8ffadeb1-8098-4d3d-a767-a60034d80393

import Mathlib

namespace RobustMDP.Discounted

theorem aux_lt2_le_fix {n : ℕ} (g : (Fin n → ℝ) → (Fin n → ℝ))
    (hmono : Monotone g) (K : NNReal) (hg : ContractingWith K g) (v : Fin n → ℝ)
    (hv : v ≤ g v) : v ≤ ContractingWith.fixedPoint g hg := by
  have hmon : Monotone fun k => g^[k] v := hmono.monotone_iterate_of_le_map hv
  have ht := ContractingWith.tendsto_iterate_fixedPoint hg v
  refine ge_of_tendsto ht (Filter.Eventually.of_forall fun k => ?_)
  have := hmon (Nat.zero_le k)
  simpa using this

end RobustMDP.Discounted

open RobustMDP.Discounted

theorem solution {n : ℕ} (q : Fin n → ℝ) (hq : 0 ≤ q) (g : (Fin n → ℝ) → (Fin n → ℝ))
    (hmono : Monotone g) (K : NNReal) (hg : ContractingWith K g) :
    ∃ vinf : Fin n → ℝ,
      g vinf = vinf ∧ (∀ w, g w = w → w = vinf) ∧
      IsGreatest ((fun v : Fin n → ℝ => ∑ i, q i * v i) '' {v | v ≤ g v})
        (∑ i, q i * vinf i) ∧
      (∀ v, v ≤ g v → v ≤ vinf) ∧
      ((∀ i, 0 < q i) →
        ∀ v, v ≤ g v → ∑ i, q i * v i = ∑ i, q i * vinf i → v = vinf) := by
  set vinf := ContractingWith.fixedPoint g hg with hvinf
  have hfix : g vinf = vinf := ContractingWith.fixedPoint_isFixedPt hg
  have hle : ∀ v, v ≤ g v → v ≤ vinf := fun v hv => aux_lt2_le_fix g hmono K hg v hv
  refine ⟨vinf, hfix, fun w hw => ContractingWith.fixedPoint_unique hg hw, ⟨?_, ?_⟩, hle, ?_⟩
  · exact ⟨vinf, by simp [hfix], rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    have h := hle v hv
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hq i)
  · intro hpos v hv hsum
    have h := hle v hv
    have h0 : ∑ i, q i * (vinf i - v i) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, hsum, sub_self]
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ q i * (vinf i - v i) :=
      fun i _ => mul_nonneg (hq i) (sub_nonneg.mpr (h i))
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0
    funext i
    have hi := hz i (Finset.mem_univ i)
    rcases mul_eq_zero.mp hi with h1 | h1
    · exact absurd h1 (ne_of_gt (hpos i))
    · linarith
