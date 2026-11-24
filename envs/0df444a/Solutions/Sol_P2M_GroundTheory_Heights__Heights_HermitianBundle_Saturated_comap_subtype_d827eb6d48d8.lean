-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianBundle_Saturated_comap_subtype_d827eb6d48d8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:27.10087+00:00
-- url     : https://prove2.me/submissions/de3153e9-960d-4a65-9424-0323198b6a28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsBundles

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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianBundle
namespace GroundTheory.Heights₂.Heights.HermitianBundle
namespace Saturated
theorem _root_.solution {M : HermitianBundle K} {G : Submodule (𝓞 K) M.carrier}
    (hG : M.Saturated G) (F : Submodule (𝓞 K) M.carrier) :
    (M.sub F).Saturated (G.comap F.subtype) := by
  intro a x ha hx
  exact hG a ((show F from x) : M.carrier) ha hx
end Saturated
end GroundTheory.Heights₂.Heights.HermitianBundle
