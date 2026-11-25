-- Prove2me | solution 1 for PI.InvTopW.tmul_natCast_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:10.065845+00:00
-- url     : https://prove2.me/submissions/6fb2421c-6bf6-4da7-ad56-cf7c819a8a96

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LinearIndependentOneBeta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_FiniteNeighbourhoodSecond
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_CoordFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
namespace PI.InvTopW
theorem _root_.solution (I : AutInst) (N : ℕ) (b : I.E) (z : Formalism.MainNotions.S.Af I.F) :
    b ⊗ₜ[I.F] ((N : Formalism.MainNotions.S.Af I.F) * z) = (N : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * (b ⊗ₜ[I.F] z) := by
  rw [← nsmul_eq_mul, ← nsmul_eq_mul, TensorProduct.tmul_smul]
end PI.InvTopW
