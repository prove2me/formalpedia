-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DivisorOneComponent_isClosed_zeroSet_e95e7da77948
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:10:50.57615+00:00
-- url     : https://prove2.me/submissions/6d7f72a1-094e-4677-a5e5-bfa178aba531

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorOneComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMultGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDivisorOneComponent

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
open MvPolynomial Filter Topology ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.DivisorOneComponent
namespace GroundTheory.Heights₂.Heights.DivisorOneComponent
theorem _root_.solution {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet K) := by
  have : zeroSet K = ⋂ f ∈ K, {x : Fin n → ℂ | eval x f = 0} := by ext x; simp [zeroSet]
  rw [this]
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const
end GroundTheory.Heights₂.Heights.DivisorOneComponent
