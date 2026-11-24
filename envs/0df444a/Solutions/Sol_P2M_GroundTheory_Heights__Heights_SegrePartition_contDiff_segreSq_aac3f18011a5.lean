-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegrePartition_contDiff_segreSq_aac3f18011a5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:49.404094+00:00
-- url     : https://prove2.me/submissions/9009d614-9295-4fac-afb0-88e70057baae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (segre)
open GroundTheory.Heights₂.Heights.SegrePartition
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.SegrePartition
theorem _root_.solution (i : (k : K) → ι k) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => segreSq z i) := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => segre z i) :=
    contDiff_prod fun k _ => contDiff_apply ℝ ℂ (⟨k, i k⟩ : Σ k, ι k)
  exact (contDiff_norm_sq ℝ).comp h
end GroundTheory.Heights₂.Heights.SegrePartition
