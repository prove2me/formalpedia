-- Prove2me | solution 1 for PI.GGMatBoundW.repGam_subrep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:40:48.262262+00:00
-- url     : https://prove2.me/submissions/cc526037-cf2e-4c2c-812b-548f20197b82

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_RepresentationDimensionPos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_IrreducibleOfMinimal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
namespace PI.GGMatBoundW
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (ψ₀ : AddChar F ℂ)
    (π : Representation ℂ (GL (Fin k) F) V) (W : Subrepresentation π) (u : W.toSubmodule) :
    ((repGam ψ₀ W.toRepresentation u : W.toSubmodule) : V) = repGam ψ₀ π (u : V) := by
  simp only [repGam, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
  first
    | rfl
    | simp
end PI.GGMatBoundW
