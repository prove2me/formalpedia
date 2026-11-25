-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_sum_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:20:24.733444+00:00
-- url     : https://prove2.me/submissions/68707519-26ec-46f8-a180-8af2475b93da

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {M : Type*} [AddCommMonoid M] {r p : ℕ} (f : Fin r → M)
    (hf : ∀ j : Fin r, ¬ (j : ℕ) < p → f j = 0) : ∑ j, f j = ∑ k : ApproxPosIdx r p, f k := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun j : Fin r => (j : ℕ) < p))
    (fun j _ hj => hf j (by simpa using hj))]
  exact Finset.sum_subtype _ (fun j => by simp) f
end ReciprocityTheory.MultiplicativeHeights
