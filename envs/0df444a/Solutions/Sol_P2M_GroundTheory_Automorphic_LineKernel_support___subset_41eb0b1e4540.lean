-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_LineKernel_support___subset_41eb0b1e4540
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:00:22.13628+00:00
-- url     : https://prove2.me/submissions/6167b038-025f-4745-bbda-05cdeb77ba6b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_tsupport_iteratedDeriv_subset
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_rem_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_support_Kc_subset
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_support_rem_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (n : ℕ) : support (ρ a r n) ⊆ Icc 0 (Rs r n) := by
  cases n with
  | zero =>
    intro t ht
    have : t ∈ Icc (r 0) (2 * r 0) := by
      by_contra h; exact ht (by simp [ρ, ηC, rem_eq_zero (hr 0) h])
    exact ⟨(hr 0).le.trans this.1, by simpa [Rs] using this.2⟩
  | succ n =>
    have hs : tsupport (KC a r n ⋆[mul ℂ ℂ] ηC a r (n + 1)) ⊆ Icc 0 (Rs r (n + 1)) := by
      refine closure_minimal ?_ isClosed_Icc
      refine (support_convolution_subset (mul ℂ ℂ)).trans ?_
      have h1 : support (KC a r n) ⊆ Icc 0 (Rs r n) := fun t ht =>
        support_Kc_subset ha hr n (by simpa [KC] using ht)
      have h2 : support (ηC a r (n + 1)) ⊆ Icc (r (n + 1)) (2 * r (n + 1)) := fun t ht =>
        support_rem_subset (hr (n + 1)) (by simpa [ηC] using ht)
      refine (Set.add_subset_add h1 h2).trans ((Set.Icc_add_Icc_subset _ _ _ _).trans
        (Icc_subset_Icc (by linarith [hr (n + 1)]) (le_of_eq ?_)))
      simp [Rs, Finset.sum_range_succ]
    intro t ht
    by_contra h
    apply ht
    simp only [ρ]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [image_eq_zero_of_notMem_tsupport (fun h' => h (hs (tsupport_iteratedDeriv_subset p h'))),
      mul_zero]
end GroundTheory.Automorphic.LineKernel
