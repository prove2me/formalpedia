-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_tailL_apply_42af02cdf323
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:30.489969+00:00
-- url     : https://prove2.me/submissions/e62247c1-f9b6-4eef-ab82-79f0c43e1d1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetPieceProductAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedFibreSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetPieceProductAnalytic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Metric Filter
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic
theorem _root_.solution {d : ℕ} (p : Fin (d + 1) → ℂ) (i : Fin d) : tailL d p i = p i.succ := rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SheetPieceProductAnalytic
