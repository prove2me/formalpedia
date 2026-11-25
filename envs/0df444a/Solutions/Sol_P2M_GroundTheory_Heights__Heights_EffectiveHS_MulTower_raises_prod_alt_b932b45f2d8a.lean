-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_prod_alt_b932b45f2d8a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:23.345525+00:00
-- url     : https://prove2.me/submissions/28e6b5f1-76ca-4b6b-aa40-bc62cbb045fd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_of_mem_06e94e5dba29
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
theorem _root_.solution {k : ℕ} (w : Fin k → A) (hw : ∀ i, w i ∈ τ.W) :
    τ.Raises k (∏ i, w i) := by
  have h := τ.raises_prod univ (fun _ => 1) w (fun i _ => τ.raises_of_mem (hw i))
  simpa using h
end GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
