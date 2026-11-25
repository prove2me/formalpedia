-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceComponents_divCycle_apply_0ef45b426d3d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:16:30.844884+00:00
-- url     : https://prove2.me/submissions/e486bbab-cabe-4939-be81-c0a7d8b7628c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartDehomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PMinimalPrimeHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLocalMultOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_POrdPolynomialLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceComponents

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
open GroundTheory.Heights₂.Heights.SliceComponents
attribute [local instance] MvPolynomial.gradedAlgebra
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.SliceComponents
theorem _root_.solution {J W : Ideal (MvPolynomial (Fin n) F)} {u : Fin n → F}
    (h : W ∈ relComps (J ⊔ Ideal.span {linForm u})) :
    divCycle J u W = localMult (J ⊔ Ideal.span {linForm u}) W := by
  classical
  simp only [divCycle, fundCycle, Finsupp.onFinset_apply]
  rw [if_pos h]
end GroundTheory.Heights₂.Heights.SliceComponents
