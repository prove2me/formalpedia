-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_detE_eq_det_fd6fff7a991a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:58:51.121877+00:00
-- url     : https://prove2.me/submissions/380eef16-2fe1-490c-bc67-bb44a2091472

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms

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
open GroundTheory.Heights₂.Heights.Inter.DiagonalForms
variable {Ω : Type*} [Field Ω] {ι : Type*} {E : Type*} [AddCommGroup E] [Module Ω E] {x : ι → Ω}
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalForms
theorem _root_.solution (e b : Module.Basis (Fin 2) Ω E) : T.detE e (b 0) (b 1) = e.det b := by
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp only [T.detE, Module.Basis.toMatrix_apply]
  ring
end GroundTheory.Heights₂.Heights.Inter.DiagonalForms
