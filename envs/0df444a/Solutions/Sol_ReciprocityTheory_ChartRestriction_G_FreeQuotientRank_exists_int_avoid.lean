-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.exists_int_avoid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:27.599546+00:00
-- url     : https://prove2.me/submissions/5a74319c-3bab-46ed-a275-b395f0f6af5f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BetaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BetaPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Finset
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution {f : ℕ} (Z : Finset (Fin f → ℝ)) (hZ : ∀ z ∈ Z, z ≠ 0) :
    ∃ t : Fin f → ℤ, ∀ z ∈ Z, ∑ j, z j * (t j : ℝ) ≠ 0 := by
  classical
  let P : (Fin f → ℝ) → Polynomial ℝ := fun z => ∑ j, Polynomial.C (z j) * Polynomial.X ^ (j : ℕ)
  have hP : ∀ z ∈ Z, P z ≠ 0 := by
    intro z hz h0
    apply hZ z hz
    funext j
    have h1 := congrArg (fun p => Polynomial.coeff p (j : ℕ)) h0
    simp only [P, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_zero] at h1
    rw [Finset.sum_eq_single j (fun i _ hij => by
      rw [if_neg (fun h => hij (Fin.ext h.symm)), mul_zero]) (by simp)] at h1
    simpa using h1
  obtain ⟨T, hT⟩ : ∃ T : ℕ, (T : ℝ) ∉ Z.biUnion (fun z => (P z).roots.toFinset) := by
    by_contra h
    push_neg at h
    have hinf : Set.Infinite (Set.range (fun n : ℕ => (n : ℝ))) :=
      Set.infinite_range_of_injective Nat.cast_injective
    exact hinf ((Z.biUnion (fun z => (P z).roots.toFinset)).finite_toSet.subset
      (by rintro _ ⟨n, rfl⟩; exact h n))
  refine ⟨fun j => (T : ℤ) ^ (j : ℕ), fun z hz h0 => ?_⟩
  apply hT
  rw [Finset.mem_biUnion]
  refine ⟨z, hz, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hP z hz), Polynomial.IsRoot]
  simp only [P, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  push_cast at h0
  exact h0
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
