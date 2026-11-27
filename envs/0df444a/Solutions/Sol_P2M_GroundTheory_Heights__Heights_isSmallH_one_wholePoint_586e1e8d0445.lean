-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isSmallH_one_wholePoint_586e1e8d0445
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:20:25.145034+00:00
-- url     : https://prove2.me/submissions/f99ccf86-2af6-4e91-ab1f-89182195bf1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_aeval_of_hom_cce1d9985939
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_whole_mkF_injective_f0f5f10d0d70


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
theorem _root_.solution [Fintype ι] (N : Geo.HermLine (blockIdx n)) :
    Geo.IsSmallH (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) (wholePoint n)) (wholePoint n) N 0 1 := by
  intro dg dh g h z _ _ _ hy _
  have hg := aeval_of_hom n (ArithVariety.whole n).mkF g
  have hh := aeval_of_hom n (ArithVariety.whole n).mkF h
  have hgh : g = h := ArithVariety.whole_mkF_injective n (by
    rw [one_mul] at hy; exact hg.symm.trans (hy.trans hh))
  subst hgh
  simp
end GroundTheory.Heights₂.Heights
