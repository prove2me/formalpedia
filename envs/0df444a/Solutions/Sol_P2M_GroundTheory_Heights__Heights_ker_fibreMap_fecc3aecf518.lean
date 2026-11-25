-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ker_fibreMap_fecc3aecf518
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:33:13.740316+00:00
-- url     : https://prove2.me/submissions/36d99662-d39a-437a-a0d3-ba90bce3e6d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreTor

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {σ ι : Type*} (t : σ → ℂ) :
    RingHom.ker (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) =
      (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) :=
  MvPolynomial.ker_map _
end GroundTheory.Heights₂.Heights
