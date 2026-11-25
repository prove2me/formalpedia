-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_aeval_mem_closure_0de02a98dc7e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:50:09.859911+00:00
-- url     : https://prove2.me/submissions/0b152043-d039-40d3-be7f-3e3de6f102bc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PEvalKerKrullDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFibreMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_SemipositiveHeights_FibreDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ForSecondHalf
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.ForSecondHalf.FibreTranscendenceDegree
namespace GroundTheory.Heights₂.Heights.ForSecondHalf.FibreTranscendenceDegree
theorem _root_.solution {σ : Type} {L : Type} [Field L] (y : σ → L) (f : MvPolynomial σ ℤ) :
    aeval y f ∈ Subfield.closure (Set.range y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [intCast_mem]
  | add f g hf hg => simpa using add_mem hf hg
  | mul_X f i hf => simpa using mul_mem hf (Subfield.subset_closure ⟨i, rfl⟩)
end GroundTheory.Heights₂.Heights.ForSecondHalf.FibreTranscendenceDegree
