-- Prove2me | solution 1 for PIW.AdelClassFin.hl_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:19:37.216316+00:00
-- url     : https://prove2.me/submissions/72023643-6020-4049-9b7e-f5e0c2fd8200

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.UG NumberField
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PIW.AdelClassFin
theorem _root_.solution : HL E 0 := by
  intro d _
  refine ⟨{((0 : Matrix (Fin 0) (Fin 0) E), (⊥ : Submodule (𝓞 E) (Fin 0 → E)))},
    Set.finite_singleton _, fun p _ => ⟨_, rfl, 1, Matrix.ext fun i _ => Fin.elim0 i, fun v => ?_⟩⟩
  have hv : v = 0 := funext fun i => Fin.elim0 i
  subst hv
  constructor
  · intro _
    exact ⟨0, Submodule.zero_mem _, funext fun i => Fin.elim0 i⟩
  · intro _
    exact Submodule.zero_mem _
end PIW.AdelClassFin
