-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCurve_full_3c2dbdc5d679
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:32:17.044652+00:00
-- url     : https://prove2.me/submissions/37a7ce6c-ed48-41e5-a1de-694231997ea0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_isPrime_orbitIdeal_50bb33dec3b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_isMultiHomogIdeal_orbitIdeal_5ad0b5ef0050
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_isRelevant_orbitIdeal_7694845330c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_isHorizontal_orbitIdeal_fbfadf85b618
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_ringKrullDim_orbitIdeal_cc019d8891ab

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G Algebra
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace OrbitCurve
theorem _root_.solution : OrbitCurve.Statement := by
  intro ι _ _ _ n x hx
  exact ⟨inferInstance, ⟨OrbitCurve.isPrime_orbitIdeal x, OrbitCurve.isMultiHomogIdeal_orbitIdeal x,
    OrbitCurve.isRelevant_orbitIdeal hx⟩, OrbitCurve.isHorizontal_orbitIdeal x,
    OrbitCurve.ringKrullDim_orbitIdeal hx⟩
end OrbitCurve
end GroundTheory.Heights₂.Heights
