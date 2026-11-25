-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.pieceN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:45:12.613087+00:00
-- url     : https://prove2.me/submissions/a874b173-5204-47af-9cce-7448ff571eba

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetOneAddSmulSingleSame
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_deriv_piece
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_one_add_smul_fromBlocks
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_inG_one_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_hasDerivAt_affine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution (Θ : M2 n → ℂ) (hl : LawH Θ) (x : M2 n) (hx : InG x) (hd : DifferentiableAt ℂ Θ x)
    (β : Matrix (Fin n) (Fin n) ℂ) (hβ : βᴴ = β) :
    fderiv ℂ Θ x (fromBlocks 0 β 0 0 * x) = lam (fromBlocks 0 β 0 0) * Θ x := by
  have hc1 : (fromBlocks 0 β 0 0 : M2 n)ᴴ * JJ n + JJ n * fromBlocks 0 β 0 0 = 0 := by
    simp [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, hβ]
  have hc2 : (fromBlocks 0 β 0 0 : M2 n)ᴴ * JJ n * fromBlocks 0 β 0 0 = 0 := by
    simp [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hβ]
  have key := deriv_piece Θ x hd (fun t : ℝ => 1 + t • (fromBlocks 0 β 0 0 : M2 n)) _
    (hasDerivAt_affine _) (by simp) (fun _ => (1 : ℂ)) 0 (hasDerivAt_const _ _)
    (Filter.Eventually.of_forall fun t => by
      have h21 : ((1 : M2 n) + t • (fromBlocks 0 β 0 0 : M2 n)).toBlocks₂₁ = 0 := by
        rw [one_add_smul_fromBlocks]
        simp
      rw [hl _ x (inG_one_add _ hc1 hc2 t) h21 hx, one_add_smul_fromBlocks]
      simp)
  rw [key]
  simp [lam]
end PositivityTheory.Rg.Sw.LVs.II
