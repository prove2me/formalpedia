-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.khw_extract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:26:50.417377+00:00
-- url     : https://prove2.me/submissions/10d42806-0dd0-413c-8a7a-64422291ae46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tcoef_tmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tcoef_map_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tcoef_lTensor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tcoef_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tcoef_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dot_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dot_root_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coord_comp_sg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coord_wt_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sg_raise_wt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ} {y : TensorProduct ℂ M (Fock n)}
    (hy : IsKHWVec ε (fun a b => TensorProduct.map (E a b) LinearMap.id +
      LinearMap.lTensor M (sgE ε cpFock cmFock a b)) μ y) (hy0 : y ≠ 0) :
    ∃ s, tcoef ((fockBasis n).coord s) y ≠ 0 ∧
      IsKHWVec ε E (μ - fockWt ε s) (tcoef ((fockBasis n).coord s) y) := by
  classical
  have hne : ∃ s, tcoef ((fockBasis n).coord s) y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hy0
    rw [tcoef_expand y]
    simp [hcon]
  obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun t => tcoef ((fockBasis n).coord t) y ≠ 0)
    (fun t => dot (fockWt ε t) lam)
    (by obtain ⟨t, ht⟩ := hne; exact ⟨t, by simpa using ht⟩)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs hmin
  have hbasis : ∀ (t : Finset (Fin (n * n))) (c : Fin n),
      sgE ε cpFock cmFock c c (fockBasis n t) = ((fockWt ε t c : ℝ) : ℂ) • fockBasis n t := by
    intro t c
    apply (fockBasis n).ext_elem
    intro u
    have h := LinearMap.congr_fun (coord_comp_sg ε u c) (fockBasis n t)
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply, LinearMap.smul_apply,
      smul_eq_mul] at h
    rw [h, map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs with htu <;> simp [htu]
  have htc : ∀ (φ : Module.Dual ℂ (Fock n)),
      tcoef φ y = ∑ t, φ (fockBasis n t) • tcoef ((fockBasis n).coord t) y := by
    intro φ
    conv_lhs => rw [tcoef_expand y]
    simp [map_sum, tcoef_tmul]
  refine ⟨s, hs, ?_⟩
  unfold IsKHWVec
  refine ⟨fun a => ?_, fun a b hab heq => ?_⟩
  · have h1 := congrArg (tcoef ((fockBasis n).coord s)) (hy.1 a)
    simp only [LinearMap.add_apply, map_add, tcoef_map_left, tcoef_lTensor, coord_comp_sg,
      tcoef_smul, map_smul] at h1
    rw [Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h1]
    abel
  · have h1 := congrArg (tcoef ((fockBasis n).coord s)) (hy.2 a b hab heq)
    simp only [LinearMap.add_apply, map_add, tcoef_map_left, tcoef_lTensor, map_zero] at h1
    have h2 : tcoef ((fockBasis n).coord s ∘ₗ sgE ε cpFock cmFock a b) y = 0 := by
      rw [htc]
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases hyt : tcoef ((fockBasis n).coord t) y = 0
      · rw [hyt, smul_zero]
      · have hco : ((fockBasis n).coord s ∘ₗ sgE ε cpFock cmFock a b) (fockBasis n t) = 0 := by
          by_contra hne'
          have hw := coord_wt_eq ε (fun c => sg_raise_wt ε (ne_of_lt hab) heq (hbasis t) c) hne'
          have hft : fockWt ε t = fockWt ε s - root a b := eq_sub_of_add_eq hw
          have hlt : dot (fockWt ε t) lam < dot (fockWt ε s) lam := by
            rw [hft, dot_sub_left, dot_root_left]
            have := hlam hab
            linarith
          exact absurd (hmin t hyt) (not_le.2 hlt)
        rw [hco, zero_smul]
    rw [h2, add_zero] at h1
    exact h1
end ReciprocityTheory.ChartRestriction.DS
