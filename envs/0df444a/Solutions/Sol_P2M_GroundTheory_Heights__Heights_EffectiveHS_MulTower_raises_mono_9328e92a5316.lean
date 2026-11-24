-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_mono_9328e92a5316
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:14.027108+00:00
-- url     : https://prove2.me/submissions/25f21a45-afb5-4023-ac16-f5f599e1b6cb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_of_mem_06e94e5dba29
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_Raises_pow_f43fcada5b6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_prod_2ebb31936f55

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
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (τ : MulTower R A)
namespace GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
theorem _root_.solution {D : ℕ} {s : Fin D → A} (hs : ∀ i, s i ∈ τ.W) (α : Fin D → ℕ) :
    τ.Raises (∑ i, α i) (mono s α) := by
  have h := τ.raises_prod univ (fun i => 1 * α i) (fun i => s i ^ α i)
    (fun i _ => (τ.raises_of_mem (hs i)).pow (α i))
  simpa [mono] using h
end GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
