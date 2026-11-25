-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.sum_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:32:06.474133+00:00
-- url     : https://prove2.me/submissions/5e4e03d5-b0c1-472a-9545-6d314cd32287

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open NumberField IsDedekindDomain Filter Topology
variable (K : Type*) [Field K] [NumberField K]
open DedekindZetaReal
open ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
namespace ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
theorem _root_.solution {s : ℝ} (u : Finset ℕ) :
    ∑ n ∈ u, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) =
      ∑ I ∈ u.biUnion (fun n ↦ (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).toFinset),
        (Ideal.absNorm I : ℝ) ^ (-s) := by
  classical
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun n _ ↦ ?_
    have hfin := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n
    have hc : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} = hfin.toFinset.card :=
      Nat.card_eq_card_finite_toFinset hfin
    rw [Finset.sum_congr rfl (g := fun _ ↦ (n : ℝ) ^ (-s)) (fun I hI ↦ by
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hI
      rw [hI]), Finset.sum_const, nsmul_eq_mul, hc]
  · intro n _ m _ hnm
    refine Finset.disjoint_left.mpr fun I h1 h2 ↦ hnm ?_
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at h1 h2
    exact h1.symm.trans h2
end ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
