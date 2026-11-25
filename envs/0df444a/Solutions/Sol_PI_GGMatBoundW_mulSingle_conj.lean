-- Prove2me | solution 1 for PI.GGMatBoundW.mulSingle_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:40:22.791204+00:00
-- url     : https://prove2.me/submissions/fa11f850-c476-4a6e-b163-94873e560e81

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_JointEigenvectorExists

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
variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}
namespace PI.GGMatBoundW
theorem _root_.solution (v : ι) (g : ∀ v, GL (Fin k) (Fq v)) (y : GL (Fin k) (Fq v)) :
    g * Pi.mulSingle v y * g⁻¹ = Pi.mulSingle v (g v * y * (g v)⁻¹) := by
  funext w
  by_cases h : w = v
  · subst h; simp
  · simp [Pi.mulSingle_eq_of_ne h]
end PI.GGMatBoundW
