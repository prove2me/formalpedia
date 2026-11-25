-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceComponents_isHomogIdeal_sup_linForm_478a4eaaa94c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:16:34.07719+00:00
-- url     : https://prove2.me/submissions/84f862b9-4bac-4eef-b913-557fe03d4dfc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartDehomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PMinimalPrimeHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLocalMultOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_POrdPolynomialLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceComponents
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocDomain_linForm_isHomogeneous_618f3987ba84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_isHomogeneous_degree_aea066f22143


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
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) F)} (hJ : IsHomogIdeal J) (u : Fin n → F) :
    IsHomogIdeal (J ⊔ Ideal.span {linForm u}) := by
  rw [isHomogIdeal_iff_isHomogeneous_degree] at hJ ⊢
  refine hJ.sup (Ideal.homogeneous_span _ _ fun x hx => ?_)
  rw [Set.mem_singleton_iff.mp hx]
  exact ⟨1, (mem_homogeneousSubmodule _ _).mpr (ChartLocDomain.linForm_isHomogeneous u)⟩
end GroundTheory.Heights₂.Heights.SliceComponents
