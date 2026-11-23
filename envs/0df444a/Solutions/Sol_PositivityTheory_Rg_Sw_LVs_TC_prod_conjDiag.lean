-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.prod_conjDiag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:36.709521+00:00
-- url     : https://prove2.me/submissions/bb4184be-e21d-45e7-8e6b-630520bae9a8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatC
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_cmI_mul_cm
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_cm_mul_cmI


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution (d1 d2 : Fin n → ℂ) (h1 : ∀ a, d1 a ≠ 0) (h2 : ∀ a, d2 a ≠ 0) :
    Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n *
      (Cm n * fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) * CmI n) = 1 := by
  set D : M2 n := fromBlocks (diagonal d1) 0 0 (diagonal d2) with hD
  set D' : M2 n := fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) with hD'
  have hDD : D * D' = 1 := by
    rw [hD, hD', fromBlocks_multiply, ← fromBlocks_one]
    simp [diagonal_mul_diagonal, h1, h2]
    done
  calc Cm n * D * CmI n * (Cm n * D' * CmI n) = Cm n * D * (CmI n * Cm n) * D' * CmI n := by
        simp only [Matrix.mul_assoc]
    _ = Cm n * (D * D') * CmI n := by
        rw [cmI_mul_cm, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hDD, Matrix.mul_one, cm_mul_cmI]
end PositivityTheory.Rg.Sw.LVs.TC
