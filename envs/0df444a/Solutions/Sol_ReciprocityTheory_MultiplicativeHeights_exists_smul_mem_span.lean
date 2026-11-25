-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.exists_smul_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:02:03.160575+00:00
-- url     : https://prove2.me/submissions/31244f73-5ee7-4b77-ad22-b53254af5397

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBB

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
open Matrix NumberField
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (x : Fin r → K) (hx : x ∈ Submodule.span K (Set.range b)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 K) (Set.range b) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
  obtain ⟨⟨d, hd⟩, hdc⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) Finset.univ c
  refine ⟨d, nonZeroDivisors.ne_zero hd, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨e, he⟩ := hdc i (Finset.mem_univ i)
  have h1 : d • (c i • b i) = e • b i := by
    rw [← smul_assoc, ← algebraMap_smul K e (b i), he]
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end ReciprocityTheory.MultiplicativeHeights
