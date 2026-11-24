-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_hermLine_ext_b7bdcdc64384
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:08.104733+00:00
-- url     : https://prove2.me/submissions/2d4ad1b1-7e31-4c62-a955-19bdffdc5952

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ThmIExists
theorem _root_.solution {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl
end GroundTheory.Heights₂.Heights.Inter.ThmIExists
