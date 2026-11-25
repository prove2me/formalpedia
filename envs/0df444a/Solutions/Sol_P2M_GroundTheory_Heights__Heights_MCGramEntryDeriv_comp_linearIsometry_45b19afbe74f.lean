-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCGramEntryDeriv_comp_linearIsometry_45b19afbe74f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:14.741432+00:00
-- url     : https://prove2.me/submissions/f51366ab-215e-4de8-b1c9-af409334b13a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PGramEntryDeriv

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
open Matrix
open GroundTheory.Heights₂.Heights.MCGramEntryDeriv
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GroundTheory.Heights₂.Heights.MCGramEntryDeriv
theorem _root_.solution {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (L : F' →ₗᵢ[ℝ] ℂ) (φ : F' → ℂ) (hφ : ∀ x, L x = φ x) {f : E → F'} {p : E}
    (hf : DifferentiableAt ℝ f p) :
    DifferentiableAt ℝ (fun q => φ (f q)) p ∧
      ‖fderiv ℝ (fun q => φ (f q)) p‖ = ‖fderiv ℝ f p‖ := by
  have hfun : (fun q => φ (f q)) = fun q => L (f q) := funext fun q => (hφ _).symm
  have hL : HasFDerivAt (fun q => L (f q)) (L.toContinuousLinearMap.comp (fderiv ℝ f p)) p :=
    L.toContinuousLinearMap.hasFDerivAt.comp p hf.hasFDerivAt
  rw [hfun]
  exact ⟨hL.differentiableAt, by rw [hL.fderiv, L.norm_toContinuousLinearMap_comp]⟩
end GroundTheory.Heights₂.Heights.MCGramEntryDeriv
