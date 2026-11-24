-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_isMultiHomog_Xbase_pow_b31bf8e0bc36
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:07.823799+00:00
-- url     : https://prove2.me/submissions/0b9e6b5a-3ec3-406c-a32d-2d1704d297d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffPair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOffFrame
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_X_3253346bc4cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_of_eq_4cde1a2b5f0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_isMultiHomog_pow_dbc197f278ca


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
theorem _root_.solution (j : ι) (M : ℕ) :
    IsMultiHomog ((X ⟨T.WBlk.base, j⟩ : MRing (T.wwIdx ι ν κ)) ^ M) (T.wwDeg M 0) :=
  DiagonalForms.isMultiHomog_of_eq
    (DiagonalForms.isMultiHomog_pow (DiagonalForms.isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.base j) M)
    (by funext b; cases b <;> simp [T.wwDeg])
end GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
