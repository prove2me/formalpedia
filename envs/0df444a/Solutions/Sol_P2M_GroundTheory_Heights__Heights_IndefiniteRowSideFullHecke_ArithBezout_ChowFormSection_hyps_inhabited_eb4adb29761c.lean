-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_ChowFormSection_hyps_inhabited_eb4adb29761c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:07:35.316475+00:00
-- url     : https://prove2.me/submissions/6688c20e-86b3-4d6d-9e57-c9e01b0c4c1d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LatticePointLogCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_isIntChowForm_detForm_88331c004274
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_linForm_ne_zero_922cf3447b3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_isArithVar_projLine__cd77cc611d02

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
namespace ChowFormSection
theorem _root_.solution :
    IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (0 + 1 + 1) ∧
      IsIntChowForm (⊥ : Ideal (MRing (PBlk 2))) (0 + 1) 1 (detForm ℤ) ∧
        linForm (![1, 0] : Fin 2 → ℤ) ∉ (⊥ : Ideal (MRing (PBlk 2))) :=
  ⟨isArithVar_projLine', isIntChowForm_detForm, linForm_ne_zero⟩
end ChowFormSection
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
