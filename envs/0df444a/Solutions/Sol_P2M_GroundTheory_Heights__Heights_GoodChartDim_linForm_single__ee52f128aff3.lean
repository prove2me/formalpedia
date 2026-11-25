-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodChartDim_linForm_single__ee52f128aff3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:52:39.754331+00:00
-- url     : https://prove2.me/submissions/f3a1f04c-d3b5-480a-b2a5-b9ae49ed277e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeVanishingHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeSliceIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDehomogPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartDehomog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartDim
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)
open GroundTheory.Heights₂.Heights.GoodChartDim
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.GoodChartDim
theorem _root_.solution {m : ℕ} (a : Fin m) : linForm (Pi.single a (1 : ℂ)) = X a := by
  classical
  simp [linForm, Pi.single_apply]
end GroundTheory.Heights₂.Heights.GoodChartDim
