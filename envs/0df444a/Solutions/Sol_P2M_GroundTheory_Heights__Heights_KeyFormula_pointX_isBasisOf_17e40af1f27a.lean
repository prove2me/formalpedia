-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_pointX_isBasisOf_17e40af1f27a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:37.789084+00:00
-- url     : https://prove2.me/submissions/1b04622d-3d83-4c0a-b890-d3e7c8b9324d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ZeroSetFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_ResidueChartModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Matrix MvPolynomial
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman (Poly GradedMod Xprod polyPiece polyGraded)
noncomputable section
attribute [instance] ResidueChartModel.grp ResidueChartModel.modP ResidueChartModel.modC
  ResidueChartModel.tower
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution : pointForm.IsBasisOf 3 pointX := by
  refine ⟨fun i => mem_thetaSec_siegelPtZero 3 _, ?_, ?_⟩
  · have : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
    rw [linearIndependent_unique_iff]
    intro h
    have := congrFun h 0
    simp [pointX] at this
  · refine le_antisymm (Submodule.span_le.2 ?_) fun f _ => ?_
    · rintro _ ⟨i, rfl⟩; exact mem_thetaSec_siegelPtZero 3 _
    · have hf : f = f 0 • pointX 0 := funext fun z => by
        simp [pointX, pointForm_fn_eq z 0]
      rw [hf]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
end GroundTheory.Heights₂.Heights.KeyFormula
