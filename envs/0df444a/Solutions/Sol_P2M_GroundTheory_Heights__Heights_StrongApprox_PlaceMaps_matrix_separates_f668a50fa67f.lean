-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_matrix_separates_f668a50fa67f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:19:30.120378+00:00
-- url     : https://prove2.me/submissions/5026fca9-71fa-44b0-811e-a61901cac2c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_separates_7b711f540c86

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
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
theorem _root_.solution {N : ℕ} (X Y : Matrix (Fin N) (Fin N) (AE F E))
    (h : ∀ v, X.map (compAt E v) = Y.map (compAt E v)) : X = Y := by
  ext i j
  exact compAt_separates _ _ fun v => congrFun (congrFun (h v) i) j
end GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
