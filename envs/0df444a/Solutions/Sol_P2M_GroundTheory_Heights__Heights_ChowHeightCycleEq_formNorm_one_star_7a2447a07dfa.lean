-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_formNorm_one_star_7a2447a07dfa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:24.740189+00:00
-- url     : https://prove2.me/submissions/6fb383ae-31de-42e6-af65-5cca8e9665ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_norm_fe0404d8d94b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_std_eq_ofPointMatrix_one_d852079b1f83


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
open MvPolynomial MeasureTheory NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ChowHeightCycleEq
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChowHeightCycleEq
theorem _root_.solution (u : Fin n → ℂ) :
    IndefiniteRowSideFullHecke.ArithBezout.formNorm (1 : Matrix (Fin n) (Fin n) ℂ) (star u) =
      IndefiniteRowSideFullHecke.ArithBezout.formNorm 1 u := by
  rw [← ObjectsHeight.ofPointMatrix_norm 1 isUnit_one, ← ObjectsHeight.ofPointMatrix_norm 1 isUnit_one,
    ← ObjectsHeight.std_eq_ofPointMatrix_one]
  exact (ArchData.std ℚ n).conj_norm (Rat.castHom ℂ) u
end GroundTheory.Heights₂.Heights.ChowHeightCycleEq
