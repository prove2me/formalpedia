-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_reads_wholePoint_77686a288d68
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:12:39.803483+00:00
-- url     : https://prove2.me/submissions/7d65b762-cdc0-44c6-852a-3216ea5dc090

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_aeval_of_hom_cce1d9985939

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (n)
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (a : ι → ℤ) (t : (ArithVariety.whole n).FunField) :
    (ArithVariety.whole n).Reads (wholePoint n) a t t := by
  intro g h _ _ _ _ _
  have hg := aeval_of_hom n (ArithVariety.whole n).mkF g
  have hh := aeval_of_hom n (ArithVariety.whole n).mkF h
  exact ⟨fun e ↦ hg.symm.trans (e.trans (congrArg _ hh)),
    fun e ↦ hg.trans (e.trans (congrArg _ hh.symm))⟩
end GroundTheory.Heights₂.Heights
