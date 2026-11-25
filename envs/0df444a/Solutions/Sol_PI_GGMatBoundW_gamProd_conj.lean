-- Prove2me | solution 1 for PI.GGMatBoundW.gamProd_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:54.093944+00:00
-- url     : https://prove2.me/submissions/994c9884-4602-43c8-86bf-5b67207adfa6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_JointEigenvectorExists
import Theorems.Thm_PI_GGConvScalarW_gam_conj


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
theorem _root_.solution (ψ : ∀ v, AddChar (Fq v) ℂ) (g x : ∀ v, GL (Fin k) (Fq v)) :
    gamProd ψ (g * x * g⁻¹) = gamProd ψ x := by
  unfold gamProd
  refine Finset.prod_congr rfl fun v _ => ?_
  exact PI.GGConvScalarW.gam_conj (ψ v) (g v) (x v)
end PI.GGMatBoundW
