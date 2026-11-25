-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_span_sup_sq_of_polyDiff_mem_39a5af881036
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:25.115181+00:00
-- url     : https://prove2.me/submissions/e4ea3cb7-5878-4255-a3b2-2155ce1a5d72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_sq_of_polyDiff_eq_zero_3e662a2d8d5a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Module
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (p : Fin n → ℂ) {ι : Type*} [Fintype ι]
    (h : ι → MvPolynomial (Fin n) ℂ) (hh : ∀ i, eval p (h i) = 0) {f : MvPolynomial (Fin n) ℂ}
    (hf : eval p f = 0) (hd : polyDiff p f ∈ Submodule.span ℂ (Set.range (polyDiff p ∘ h))) :
    f ∈ Ideal.span (Set.range h) ⊔ RingHom.ker (eval p) ^ 2 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hd
  have hg0 : eval p (f - ∑ i, C (c i) * h i) = 0 := by simp [hf, hh]
  have hg1 : polyDiff p (f - ∑ i, C (c i) * h i) = 0 := by
    simp only [map_sub, map_sum, C_mul', map_smul]
    rw [← hc]
    simp
  have hsum : ∑ i, C (c i) * h i ∈ Ideal.span (Set.range h) :=
    sum_mem fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have e : f = (f - ∑ i, C (c i) * h i) + ∑ i, C (c i) * h i := by ring
  rw [e]
  exact add_mem (Ideal.mem_sup_right (mem_sq_of_polyDiff_eq_zero p hg0 hg1))
    (Ideal.mem_sup_left hsum)
end GroundTheory.Heights₂.Heights
