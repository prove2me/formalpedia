-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homogenize_d7e21fc8680f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:37.419646+00:00
-- url     : https://prove2.me/submissions/0877bf82-de37-4b3f-8b68-7fa343f8b117

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_yyc_base_29c3d2390e14
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_aeval_Xpow_33fd54a9e382
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_Xpow_homog_6fdb90b2f59f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {D : ℕ} (S : ProjectiveLineBundle D)
namespace GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
theorem _root_.solution (i : S.ι) (hx : S.x i ≠ 0) {a : S.Ω} (ha : a ∈ chartRing ℤ S.x i) :
    ∃ (d : ℕ) (P : MRing S.YIdx), IsWeightedHomogeneous (wt S) P (Pi.single .base d) ∧
      aeval (yyc S) P = algebraMap S.Ω S.Φ (a * S.x i ^ d) := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    refine ⟨1, X ⟨.base, j⟩, isWeightedHomogeneous_X ℤ _ _, ?_⟩
    rw [aeval_X, yyc_base, pow_one, div_mul_cancel₀ _ hx]
  | algebraMap n =>
    refine ⟨0, C n, ?_, ?_⟩
    · rw [Pi.single_zero]
      exact isWeightedHomogeneous_C _ _
    · simp
  | add y z _ _ hy hz =>
    obtain ⟨d1, P1, h1, e1⟩ := hy
    obtain ⟨d2, P2, h2, e2⟩ := hz
    refine ⟨d1 + d2, P1 * X ⟨.base, i⟩ ^ d2 + P2 * X ⟨.base, i⟩ ^ d1, ?_, ?_⟩
    · rw [Pi.single_add]
      refine IsWeightedHomogeneous.add (h1.mul (Xpow_homog S i d2)) ?_
      rw [add_comm]
      exact h2.mul (Xpow_homog S i d1)
    · rw [map_add, map_mul, map_mul, aeval_Xpow, aeval_Xpow, e1, e2, ← map_mul, ← map_mul, ← map_add]
      congr 1
      ring
  | mul y z _ _ hy hz =>
    obtain ⟨d1, P1, h1, e1⟩ := hy
    obtain ⟨d2, P2, h2, e2⟩ := hz
    refine ⟨d1 + d2, P1 * P2, ?_, ?_⟩
    · rw [Pi.single_add]
      exact h1.mul h2
    · rw [map_mul, e1, e2, ← map_mul]
      congr 1
      ring
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
