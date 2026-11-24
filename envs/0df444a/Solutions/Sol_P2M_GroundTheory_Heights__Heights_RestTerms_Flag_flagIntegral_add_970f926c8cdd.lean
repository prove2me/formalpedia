-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_add_970f926c8cdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:34.778674+00:00
-- url     : https://prove2.me/submissions/6715216f-51b9-44aa-8e02-2010be77ddf9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic

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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
variable (f r a : ℕ) (c : SmallBlock)
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution (f N : ℕ) (Φ Ψ : RootRing f N) :
    flagIntegral f N (Φ + Ψ) = flagIntegral f N Φ + flagIntegral f N Ψ := by
  simp only [flagIntegral, coeff_add, add_mul, Finset.sum_add_distrib]
end GroundTheory.Heights₂.Heights.RestTerms.Flag
