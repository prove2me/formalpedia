-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homogenize_fam_b09891dd724c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:12.851228+00:00
-- url     : https://prove2.me/submissions/051711ad-0238-453e-9fe6-a7d743e2149a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_aeval_Xpow_33fd54a9e382
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_Xpow_homog_6fdb90b2f59f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homogenize_d7e21fc8680f

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
theorem _root_.solution (i : S.ι) (hx : S.x i ≠ 0) {α : Type} [Fintype α] (a : α → S.Ω)
    (ha : ∀ t, a t ∈ chartRing ℤ S.x i) :
    ∃ (d : ℕ) (P : α → MRing S.YIdx), ∀ t, IsWeightedHomogeneous (wt S) (P t) (Pi.single .base d) ∧
      aeval (yyc S) (P t) = algebraMap S.Ω S.Φ (a t * S.x i ^ d) := by
  classical
  choose d P hP eP using fun t => homogenize S i hx (ha t)
  refine ⟨∑ t, d t, fun t => X ⟨.base, i⟩ ^ (∑ t, d t - d t) * P t, fun t => ⟨?_, ?_⟩⟩
  · have hle : d t ≤ ∑ t, d t := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    have := (Xpow_homog S i (∑ t, d t - d t)).mul (hP t)
    rwa [← Pi.single_add, Nat.sub_add_cancel hle] at this
  · have hle : d t ≤ ∑ t, d t := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    rw [map_mul, aeval_Xpow, eP t, ← map_mul]
    congr 1
    rw [← pow_sub_mul_pow (S.x i) hle]
    ring
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
