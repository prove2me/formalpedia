-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceComponents_mem_support_divCycle_2640b9484206
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:50.555153+00:00
-- url     : https://prove2.me/submissions/8c9f3311-ae5f-4f3d-b1a9-1316835e11b5

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
theorem _root_.solution {J W : Ideal (MvPolynomial (Fin n) F)} {u : Fin n → F} :
    W ∈ (divCycle J u).support ↔
      W ∈ relComps (J ⊔ Ideal.span {linForm u}) ∧ localMult (J ⊔ Ideal.span {linForm u}) W ≠ 0 := by
  classical
  simp only [divCycle, fundCycle, Finsupp.mem_support_iff, Finsupp.onFinset_apply]
  split_ifs with h <;> simp [h]
end GroundTheory.Heights₂.Heights.SliceComponents
