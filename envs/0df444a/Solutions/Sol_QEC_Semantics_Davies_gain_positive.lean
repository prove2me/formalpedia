-- Prove2me | solution 1 for QEC.Semantics.Davies.gain_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:06:46.448872+00:00
-- url     : https://prove2.me/submissions/54a4df7e-205c-4a60-9914-50e5ab505385

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_Davies_TraceBound

set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]
namespace QEC.Semantics.Davies
theorem _root_.solution (J : κ → Operator V) (F : Operator V) (hF : F.IsPositive) :
    (lindbladJumpGain J F).IsPositive := by
  apply LinearMap.isPositive_sum Finset.univ
  intro a _
  exact hF.conj_adjoint (J a)
end QEC.Semantics.Davies
