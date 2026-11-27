-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_setting_inhabited_56f02d49d4cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:02:26.980202+00:00
-- url     : https://prove2.me/submissions/72cd8324-48e2-4677-8df9-b3f92e57dccc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_ofMetrics_fs_afa86c0133a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ex_isXi_a6edbafecd63
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ex_fromBase_6170f3c4c5d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ex_isPull0_9061b183e0fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ex_isPull1_267d9c1079da

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ComplexOrder ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
attribute [instance] ProjectiveLineBundle.fieldΩ ProjectiveLineBundle.finι ProjectiveLineBundle.finν ProjectiveLineBundle.finκ ProjectiveLineBundle.acgE ProjectiveLineBundle.modE
  ProjectiveLineBundle.fieldΦ ProjectiveLineBundle.algΦ
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution :
    ∃ (S : ProjectiveLineBundle 1) (X A : HermLine S.YIdx) (X₀ X₁ A₀ : HermLine S.WIdx),
      S.IsXi X ∧ IsSmoothHerm A ∧ IsFromBase A ∧
      IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) X X₀ ∧ IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) X X₁ ∧
      IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀ ∧
      IsSmoothHerm X₀ ∧ IsSmoothHerm X₁ ∧ IsSmoothHerm A₀ :=
  ⟨projLineBundleExample, exXi, exAL, exPull 0 T.twoXiDegY, exPull 1 T.twoXiDegY, exPull 0 (Pi.single T.YBlk.base 1),
    ex_isXi, isSmoothHerm_ofMetrics_fs _, ex_fromBase, ex_isPull0 _, ex_isPull1 _, ex_isPull0 _,
    isSmoothHerm_ofMetrics_fs _, isSmoothHerm_ofMetrics_fs _, isSmoothHerm_ofMetrics_fs _⟩
end GroundTheory.Heights₂.Heights.Inter
