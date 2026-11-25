-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.mMap_sm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:18.062882+00:00
-- url     : https://prove2.me/submissions/72ce47a7-9925-45fb-b9b9-9de5398b788d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Smooth
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_conjT
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_fromBlocks
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_fromRows
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_fromCols
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_reindex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution {k j ρ : ℕ} {M : X → Matrix (Fin j) (Fin j) ℂ} (hM : ContDiffAt ℝ n M x₀)
    (hdet : (M x₀).det ≠ 0) (γ : B.Mat k ρ) : ContDiffAt ℝ n (fun x => mMap k j ρ (M x) γ) x₀ := by
  have hdet' : ((M x₀)ᴴ).det ≠ 0 := by
    rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hdet
  simp only [mMap, blk3]
  refine sm_reindex _ _ (sm_fromBlocks contDiffAt_const ?_ ?_ contDiffAt_const)
  · exact sm_fromRows (sm_mul (sm_inv (sm_conjT hM) hdet') contDiffAt_const) contDiffAt_const
  · exact sm_fromCols (sm_mul contDiffAt_const hM) contDiffAt_const
end PI.UnitaryGroupMassFormula.UsCost
