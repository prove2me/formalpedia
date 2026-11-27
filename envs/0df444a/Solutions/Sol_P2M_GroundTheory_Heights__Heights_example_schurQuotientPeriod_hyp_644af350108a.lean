-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_example_schurQuotientPeriod_hyp_644af350108a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:11:46.493284+00:00
-- url     : https://prove2.me/submissions/f5570d33-b671-49e9-81b1-f27eb7192d8f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements

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
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    let τ : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
      Matrix.diagonal (Sum.elim (fun _ => Complex.I) (fun _ => 1 + 2 * Complex.I))
    τᵀ = τ ∧ (τ.map Complex.im).PosDef := by
  refine ⟨Matrix.diagonal_transpose _, ?_⟩
  rw [Matrix.diagonal_map (by simp)]
  exact Matrix.posDef_diagonal_iff.mpr fun k => by cases k <;> simp
end GroundTheory.Heights₂.Heights
