-- Prove2me | solution 2 for QEC.Semantics.Davies.diagonal_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:03:37.130582+00:00
-- url     : https://prove2.me/submissions/309aae64-3a15-43b6-bbbe-3c8e3b416aea

import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
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
namespace QEC.Semantics.Davies
theorem _root_.solution (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) :
    (diagonal b e).IsSymmetric :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr (diagonal_adjoint b e)
end QEC.Semantics.Davies
