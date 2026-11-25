-- Prove2me | solution 1 for PI.WGL.io_eig_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:05.819711+00:00
-- url     : https://prove2.me/submissions/1ef87615-febe-4acb-a5dc-e318f063b802

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_PeriodIntegrals_GTBranch
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoExistsOfCap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace PI.WGL
open Formalism.BasicNotions MvPolynomial
private theorem sum_eq_zero_of_eigen_separated {ι V : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    (C : ℂ → Module.End ℂ V) (p : ι → ℂ → ℂ) (i0 : ι) (hp : ∀ i, i ≠ i0 → ∃ u, p i u ≠ p i0 u)
    (G : Finset ι) (hG : i0 ∉ G) : ∀ (y : ι → V), (∀ i ∈ G, ∀ u, C u (y i) = p i u • y i) →
      (∀ u, C u (∑ i ∈ G, y i) = p i0 u • ∑ i ∈ G, y i) → ∑ i ∈ G, y i = 0 := by
  revert hG
  refine Finset.induction_on G ?_ ?_
  · intro _ y _ _
    simp
  · intro j G hj ih hjG y hy hS
    have hi0j : j ≠ i0 := fun h => hjG (h ▸ Finset.mem_insert_self j G)
    have hi0G : i0 ∉ G := fun h => hjG (Finset.mem_insert_of_mem h)
    obtain ⟨u, hu⟩ := hp j hi0j
    have hsum : (p i0 u - p j u) • ∑ i ∈ insert j G, y i = ∑ i ∈ G, (p i u - p j u) • y i := by
      have h1 : C u (∑ i ∈ insert j G, y i) - p j u • ∑ i ∈ insert j G, y i =
          (p i0 u - p j u) • ∑ i ∈ insert j G, y i := by
        rw [hS u, sub_smul]
      have h2 : C u (∑ i ∈ insert j G, y i) - p j u • ∑ i ∈ insert j G, y i =
          ∑ i ∈ G, (p i u - p j u) • y i := by
        rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.sum_insert hj,
          hy j (Finset.mem_insert_self j G) u, sub_self, zero_add]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [hy i (Finset.mem_insert_of_mem hi) u, sub_smul]
      rw [← h1, h2]
    have hzero : ∑ i ∈ G, (p i u - p j u) • y i = 0 := by
      refine ih hi0G (fun i => (p i u - p j u) • y i) ?_ ?_
      · intro i hi v
        show C v ((p i u - p j u) • y i) = p i v • ((p i u - p j u) • y i)
        rw [map_smul, hy i (Finset.mem_insert_of_mem hi) v, smul_comm]
      · intro v
        show C v (∑ i ∈ G, (p i u - p j u) • y i) = p i0 v • ∑ i ∈ G, (p i u - p j u) • y i
        rw [← hsum, map_smul, hS v, smul_comm]
    have hfin : (p i0 u - p j u) • ∑ i ∈ insert j G, y i = 0 := by
      rw [hsum, hzero]
    rcases smul_eq_zero.mp hfin with h | h
    · exact absurd (sub_eq_zero.mp h).symm hu
    · exact h
end PI.WGL
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL
theorem _root_.solution {ι V : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    (C : ℂ → Module.End ℂ V) (p : ι → ℂ → ℂ) (i0 : ι) (hp : ∀ i, i ≠ i0 → ∃ u, p i u ≠ p i0 u) :
    ∀ (F : Finset ι) (y : ι → V), (∀ i ∈ F, ∀ u, C u (y i) = p i u • y i) →
      (∀ u, C u (∑ i ∈ F, y i) = p i0 u • ∑ i ∈ F, y i) →
      ∑ i ∈ F, y i = ∑ i ∈ F.filter (fun i => i = i0), y i := by
  intro F y hy hS
  have hF := Finset.sum_filter_add_sum_filter_not F (fun i => i = i0) y
  have hz : ∑ i ∈ F.filter (fun i => ¬ i = i0), y i = 0 := by
    apply sum_eq_zero_of_eigen_separated C p i0 hp _ (by simp)
    · intro i hi u
      exact hy i (Finset.mem_filter.mp hi).1 u
    · intro u
      have h2 : ∑ i ∈ F.filter (fun i => ¬ i = i0), y i =
          ∑ i ∈ F, y i - ∑ i ∈ F.filter (fun i => i = i0), y i := by
        rw [← hF]
        abel
      have h3 : ∀ v, C v (∑ i ∈ F.filter (fun i => i = i0), y i) =
          p i0 v • ∑ i ∈ F.filter (fun i => i = i0), y i := by
        intro v
        rw [map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi' := Finset.mem_filter.mp hi
        rw [hy i hi'.1 v, hi'.2]
      rw [h2, map_sub, hS u, h3 u, smul_sub]
  rw [← hF, hz, add_zero]
end PI.WGL
