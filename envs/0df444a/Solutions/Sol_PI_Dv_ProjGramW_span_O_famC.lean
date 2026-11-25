-- Prove2me | solution 1 for PI.Dv.ProjGramW.span_O_famC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:45:05.918594+00:00
-- url     : https://prove2.me/submissions/d2fdcd43-e207-4336-872c-50e04fa1bb5b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_PI_Dv_ProjGramW_span_famC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution {d : ℕ} (b : Fin d → V) (C : Matrix (Fin d) (Fin d) K) (hC : C.det ≠ 0) :
    Submodule.span K ((Submodule.span (𝓞 K) (Set.range (famC b C)) : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K ((Submodule.span (𝓞 K) (Set.range b) : Submodule (𝓞 K) V) : Set V) := by
  rw [Submodule.span_span_of_tower, Submodule.span_span_of_tower, span_famC b C hC]
end PI.Dv.ProjGramW
