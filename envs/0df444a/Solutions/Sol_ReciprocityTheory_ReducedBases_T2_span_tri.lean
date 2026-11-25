-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.span_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:49:02.656018+00:00
-- url     : https://prove2.me/submissions/cffb9a07-3d6b-4122-8ba1-197befeba43a

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_SizeReduce

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Submodule
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {d : ℕ} (v : Fin d → M)
    (W : Fin d → Fin d → R) (hW : ∀ i l, i ≤ l → W i l = 0) (S : Set (Fin d))
    (hS : ∀ i ∈ S, ∀ l < i, l ∈ S) :
    span R (v '' S) = span R ((fun i => v i - ∑ l, W i l • v l) '' S) := by
  set w : Fin d → M := fun i => v i - ∑ l, W i l • v l with hw
  have key : ∀ i, i ∈ S → v i ∈ span R (w '' S) := by
    intro i
    refine WellFoundedLT.induction (motive := fun i => i ∈ S → v i ∈ span R (w '' S)) i ?_
    intro i ih hi
    have hv : v i = w i + ∑ l, W i l • v l := (sub_add_cancel _ _).symm
    rw [hv]
    refine Submodule.add_mem _ (Submodule.subset_span ⟨i, hi, rfl⟩)
      (Submodule.sum_mem _ fun l _ => ?_)
    by_cases hl : l < i
    · exact Submodule.smul_mem _ _ (ih l hl (hS i hi l hl))
    · rw [hW i l (not_lt.mp hl), zero_smul]
      exact Submodule.zero_mem _
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact key i hi
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    show v i - ∑ l, W i l • v l ∈ span R (v '' S)
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨i, hi, rfl⟩)
      (Submodule.sum_mem _ fun l _ => ?_)
    by_cases hl : l < i
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hS i hi l hl, rfl⟩)
    · rw [hW i l (not_lt.mp hl), zero_smul]
      exact Submodule.zero_mem _
end ReciprocityTheory.ReducedBases.T2
