-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.theta_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:05.983227+00:00
-- url     : https://prove2.me/submissions/cad8ed0e-bd80-43b0-87a7-c8913c080510

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (a b : Fin n) :
    Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε = adjSign ε a b • Matrix.single b a 1 := by
  ext i j
  simp [Jm, adjSign, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply,
    Matrix.conjTranspose_apply, Matrix.smul_apply] <;> split_ifs <;> simp_all
end ReciprocityTheory.ChartRestriction.DS
