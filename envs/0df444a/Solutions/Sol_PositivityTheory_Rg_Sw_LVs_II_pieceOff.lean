-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.pieceOff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:45:15.039958+00:00
-- url     : https://prove2.me/submissions/9a4af898-44cb-4468-888e-295883a95a3f

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
    (c : ℂ) (i j : Fin n) (hij : i ≠ j) :
    fderiv ℂ Θ x (Pij c i j * x) = lam (Pij c i j) * Θ x := by
  have hc1 : (Pij c i j)ᴴ * JJ n + JJ n * Pij c i j = 0 := by
    simp [Pij, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_single, Complex.star_def]
  have hc2 : (Pij c i j)ᴴ * JJ n * Pij c i j = 0 := by
    simp [Pij, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_single, Complex.star_def,
      Matrix.single_mul_single_of_ne, hij, Ne.symm hij]
  have hdet : ∀ t : ℝ, ((1 : Matrix (Fin n) (Fin n) ℂ) + t • (-(conj c) • Matrix.single j i 1)).det = 1 := by
    intro t
    rw [← smul_assoc, Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.det_transvection_of_ne j i (Ne.symm hij) _
  have key := deriv_piece Θ x hd (fun t : ℝ => 1 + t • Pij c i j) _
    (hasDerivAt_affine _) (by simp) (fun _ => (1 : ℂ)) 0 (hasDerivAt_const _ _)
    (Filter.Eventually.of_forall fun t => by
      have h21 : ((1 : M2 n) + t • Pij c i j).toBlocks₂₁ = 0 := by
        rw [Pij, one_add_smul_fromBlocks]
        simp
      rw [hl _ x (inG_one_add _ hc1 hc2 t) h21 hx, Pij, one_add_smul_fromBlocks,
        Matrix.toBlocks_fromBlocks₂₂, hdet]
      simp)
  rw [key]
  simp [lam, Pij, Matrix.trace_smul, Matrix.trace_single_eq_of_ne _ _ _ hij,
    Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hij)]
end PositivityTheory.Rg.Sw.LVs.II
