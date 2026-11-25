-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:05:52.276836+00:00
-- url     : https://prove2.me/submissions/267c2171-0241-4ad3-b434-7991d87bf9e0

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_DerivSmoothTransitionOfOneLt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_deriv_smoothTransition_of_neg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_deriv_smoothTransition_bounded
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_smoothReal_dbar_sq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_dbar_sq_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_dbar_sq_comp_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_continuous_of_smoothReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_tsupport_d_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : PsiStatement n M := by
  intro z hz e a he hcomp
  have hec : Continuous e := continuous_of_smoothReal n z hz e he
  obtain ⟨C, hC⟩ := deriv_smoothTransition_bounded
  set D := dbarSq n z (fun y => (e y : ℂ)) with hD
  have hDs : SmoothR n z D := smoothReal_dbar_sq n z e he
  have hk0 : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (t - a - 2)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).sub contDiff_const)
  refine ⟨fun x => Real.smoothTransition (e x - a - 2) * (C ^ 2 * D x), ?_, ?_, ?_⟩
  · refine SmoothR.mul n z _ _ (SmoothR.comp n z _ hk0 e he) (SmoothR.mul n z _ _ ?_ hDs)
    show Smooth n z (fun _ => ((C ^ 2 : ℝ) : ℂ))
    exact Smooth.const n z _
  · intro x hx
    have h0 : ∀ y, e y < a + 2 →
        Real.smoothTransition (e y - a - 2) * (C ^ 2 * D y) = 0 := by
      intro y hy
      rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
    refine ⟨h0 x (by linarith), ?_⟩
    unfold dSqR
    refine Finset.sum_eq_zero fun j _ => ?_
    have hnot : x ∉ tsupport (fun y =>
        ((Real.smoothTransition (e y - a - 2) * (C ^ 2 * D y) : ℝ) : ℂ)) := by
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [(isOpen_lt hec continuous_const).mem_nhds
        (show e x < a + 2 by linarith)] with y hy
      simp [h0 y hy]
    have hnot2 := fun h => hnot (tsupport_d_subset n z j _ h)
    rw [image_eq_zero_of_notMem_tsupport hnot2]
    simp
  · intro ν
    set N : ℝ := max (ν : ℝ) (a + 3) with hN
    have hk : ContDiff ℝ ∞ (fun t : ℝ => 1 - Real.smoothTransition (t - N)) :=
      contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))
    refine ⟨fun x => 1 - Real.smoothTransition (e x - N), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · exact SmoothR.comp n z _ hk e he
    · refine HasCompactSupport.intro (hcomp (N + 1)) fun x hx => ?_
      simp only [Set.mem_ofPred_eq, not_le] at hx
      beta_reduce
      rw [Real.smoothTransition.one_of_one_le (show 1 ≤ e x - N by linarith)]
      simp
    · intro x
      exact ⟨by linarith [Real.smoothTransition.le_one (e x - N)],
        by linarith [Real.smoothTransition.nonneg (e x - N)]⟩
    · intro x hx
      beta_reduce
      rw [Real.smoothTransition.zero_of_nonpos (show e x - N ≤ 0 by linarith [le_max_left (ν : ℝ) (a + 3)])]
      simp
    · intro x
      have hcomp' : dbarSq n z (fun y => ((1 - Real.smoothTransition (e y - N) : ℝ) : ℂ)) x =
          deriv (fun t : ℝ => 1 - Real.smoothTransition (t - N)) (e x) ^ 2 * D x :=
        dbar_sq_comp_eq n z _ hk e he x
      have hder : deriv (fun t : ℝ => 1 - Real.smoothTransition (t - N)) (e x) =
          -deriv Real.smoothTransition (e x - N) := by
        rw [deriv_const_sub, deriv_comp_sub_const]
      rw [hcomp', hder, neg_sq]
      have hD0 : 0 ≤ D x := dbar_sq_nonneg n z _ x
      by_cases hlt : e x < N
      · rw [deriv_smoothTransition_of_neg (by linarith)]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
        exact (Real.exp_pos _).le
      · have hge : a + 3 ≤ e x := le_trans (le_max_right _ _) (not_lt.1 hlt)
        beta_reduce
        rw [Real.smoothTransition.one_of_one_le (show 1 ≤ e x - a - 2 by linarith), one_mul]
        have h1 : deriv Real.smoothTransition (e x - N) ^ 2 ≤ C ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hC _) 2
        have h2 := Real.add_one_le_exp (C ^ 2 * D x)
        nlinarith
end ReciprocityTheory.L2DbarEstimates.F
