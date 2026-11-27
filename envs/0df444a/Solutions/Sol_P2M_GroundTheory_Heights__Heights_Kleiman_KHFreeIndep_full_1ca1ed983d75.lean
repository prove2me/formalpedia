-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_full_1ca1ed983d75
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:01:24.506714+00:00
-- url     : https://prove2.me/submissions/91663473-74af-4a5c-a093-e1eaef4f5672

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeIndepSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHFreeIndep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeIndep_eq_zero_of_sum_smul_monoFrac_1100fad6d4bd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace KHFreeIndep
theorem _root_.solution : KHFreeIndep.Statement := by
  intro S _ K _ _ ι _ _ n A f h a ha
  classical
  funext J
  let g : ((Σ k, ι k) → ℤ) → S := fun b =>
    if hb : ∀ k, negSet b k ⊆ J.1.1 k then f b ⟨J.1, hb⟩ else 0
  have hsum : ∑ b ∈ A, g b • monoFrac S J.1.1 b = 0 := by
    have h0 := congrFun h J.1
    rw [Finset.sum_apply, Pi.zero_apply] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [embed, LinearMap.pi_apply, g]
    split_ifs with hb1
    · rfl
    · simp [monoFrac, hb1]
  have hJ := KHFreeIndep.eq_zero_of_sum_smul_monoFrac J.1.1 A g (fun b _ hb => dif_neg hb) hsum a ha
  rw [show g a = f a J from dif_pos J.2] at hJ
  simpa using hJ
end KHFreeIndep
end GroundTheory.Heights₂.Heights.Kleiman
