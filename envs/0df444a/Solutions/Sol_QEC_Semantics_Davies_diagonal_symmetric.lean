-- Prove2me | solution 1 for QEC.Semantics.Davies.diagonal_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T14:33:15.861199+00:00
-- url     : https://prove2.me/submissions/cabd6b78-76d2-4a19-a23f-7d886a97d616

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Theorems.Thm_QEC_Semantics_Davies_diagonal_adjoint
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) :
    (diagonal b e).IsSymmetric :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr (diagonal_adjoint b e)
