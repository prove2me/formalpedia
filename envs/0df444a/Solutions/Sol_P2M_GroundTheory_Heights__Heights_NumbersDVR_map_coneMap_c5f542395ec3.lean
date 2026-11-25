-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_map_coneMap_c5f542395ec3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:43:00.375309+00:00
-- url     : https://prove2.me/submissions/99034f2a-66d4-4fe5-96f3-a646d1a7a4b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTruncSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTruncSpecialize

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {σ τ R B B' : Type*} [CommRing R] [CommRing B] [CommRing B'] (f : R →+* B)
    (g : B →+* B') (c : σ → B) (q : σ → τ) (x : MvPolynomial σ R) :
    map g (eval₂ (C.comp f) (fun p => C (c p) * X (q p)) x) =
      eval₂ (C.comp (g.comp f)) (fun p => C (g (c p)) * X (q p)) x := by
  rw [eval₂_comp_left]
  congr 1
  · exact RingHom.ext fun a => by simp
  · funext p
    simp
end GroundTheory.Heights₂.Heights.NumbersDVR
