-- Prove2me | solution 1 for ReciprocityTheory.PTheta.siegelSubDomain_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:31:15.388135+00:00
-- url     : https://prove2.me/submissions/c6609c18-df5d-4306-927c-21414a1b884e

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta
open sphereQuadraticPositivity
namespace ReciprocityTheory.PTheta
theorem _root_.solution : SiegelSubDomainStatement := by
  unfold SiegelSubDomainStatement ThetaDomain SiegelH
  intro ι _ τ hτ
  obtain ⟨hs, hp⟩ := hτ
  have ht : (τ.map Complex.im)ᵀ = τ.map Complex.im := by
    rw [← Matrix.transpose_map, hs.eq]
  show (τ.map Complex.im + (τ.map Complex.im)ᵀ).PosDef
  rw [ht]
  exact hp.add hp
end ReciprocityTheory.PTheta
