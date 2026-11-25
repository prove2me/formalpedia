-- Prove2me | solution 1 for PI.FJMD.vecJ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:58:34.953883+00:00
-- url     : https://prove2.me/submissions/c63bd085-5663-496f-bba0-2ae77b9ecf90

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Theorems.Thm_PI_FJMD_dd_eq_zero
import Theorems.Thm_PI_FJMD_hwVec_mem_supported
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix FockH1Action
namespace PI.FJMD
open PI.FJM
private theorem moduleEnd_finset_sum_apply {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*}
    (t : Finset ι) (f : ι → Module.End ℂ V) (v : V) : (∑ x ∈ t, f x) v = ∑ x ∈ t, f x v := by
  first
  | exact LinearMap.sum_apply t f v
  | simp
end PI.FJMD
end
end

set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.FJMD
open PI.FJM
namespace PI.FJMD
theorem _root_.solution (hF : FormJ) : VecJ := by
  intro p q r s a b c d h
  have hsupp := hwVec_mem_supported p q r s a b c d
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2, h3, h4⟩ := h
  refine (hF p q r s (PI.FJM.hwVec p q r s a b c d)).mpr ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    unfold PI.FJM.lapA
    rw [moduleEnd_finset_sum_apply]
    refine Finset.sum_eq_zero fun l _ => dd_eq_zero hsupp ?_
    refine not_and_or.mp ?_
    rintro ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, inS] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    omega
  · intro i j
    unfold PI.FJM.lapB
    rw [moduleEnd_finset_sum_apply]
    refine Finset.sum_eq_zero fun k _ => dd_eq_zero hsupp ?_
    refine not_and_or.mp ?_
    rintro ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, inS] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    omega
  · intro k l
    unfold PI.FJM.lapC
    rw [moduleEnd_finset_sum_apply]
    refine Finset.sum_eq_zero fun i _ => dd_eq_zero hsupp ?_
    refine not_and_or.mp ?_
    rintro ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, inS] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    omega
  · intro k l
    unfold PI.FJM.lapD
    rw [moduleEnd_finset_sum_apply]
    refine Finset.sum_eq_zero fun j _ => dd_eq_zero hsupp ?_
    refine not_and_or.mp ?_
    rintro ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, inS] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    omega
end PI.FJMD
