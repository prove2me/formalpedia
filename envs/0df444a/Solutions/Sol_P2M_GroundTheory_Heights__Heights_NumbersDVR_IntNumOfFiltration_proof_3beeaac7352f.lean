-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumOfFiltration_proof_3beeaac7352f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:24:21.49367+00:00
-- url     : https://prove2.me/submissions/e75bd52b-75f3-4a0e-b970-51a24b2722d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumOfFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumOfFiltration_eventually_mixedDiff_sum_b0957ba4a222

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
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumOfFiltration
namespace GroundTheory.Heights₂.Heights.NumbersDVR.IntNumOfFiltration
theorem _root_.solution (h1 : MixedDiffLinear.Statement) (h2 : DegLTEventuallyConst.Statement)
    (h3 : EventualValueFacts.Statement) : IntNumOfFiltration.Statement := by
  intro F _ K _ _ ι _ n J l hdeg hJ bs
  have hfun : hilbFn J = fun m => (l.map fun p => hilbFn p.1 (m - fun k => (p.2 k : ℤ))).sum :=
    funext hJ
  have hev := eventually_mixedDiff_sum h1 h3 bs
    (fun p : Ideal (MRing ι F) × (K → ℕ) => hilbFn p.1) (fun p k => (p.2 k : ℤ)) l
    (fun p hp => h2 K n (hilbFn p.1) (hdeg p hp) bs)
  unfold intNum
  rw [hfun]
  exact (h3 K _ _ 0).1 hev
end GroundTheory.Heights₂.Heights.NumbersDVR.IntNumOfFiltration
