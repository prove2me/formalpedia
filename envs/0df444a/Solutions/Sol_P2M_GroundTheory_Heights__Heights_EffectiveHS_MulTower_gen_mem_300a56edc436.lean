-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_gen_mem_300a56edc436
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:05:22.043036+00:00
-- url     : https://prove2.me/submissions/0732d0d2-87bf-4ede-ac1d-bfdf2482304d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_mono_9328e92a5316
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_raises_prod_alt_b932b45f2d8a

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
variable {D : ℕ} {s : Fin D → A}
namespace GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
theorem _root_.solution (hs : ∀ i, s i ∈ τ.W) {T : ℕ} (α : Fin D → ℕ) {k : ℕ} (w : Fin k → A)
    (hw : ∀ i, w i ∈ τ.W) {m : A} (hm : m ∈ τ.V 0) (hT : ∑ i, α i + k = T) :
    mono s α * (∏ i, w i) * m ∈ τ.V T := by
  have h := ((τ.raises_mono hs α).mul (τ.raises_prod_alt w hw)) 0 m hm
  rwa [zero_add, hT] at h
end GroundTheory.Heights₂.Heights.EffectiveHS.MulTower
