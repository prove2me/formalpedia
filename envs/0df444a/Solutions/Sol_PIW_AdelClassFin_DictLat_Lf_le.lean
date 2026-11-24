-- Prove2me | solution 1 for PIW.AdelClassFin.DictLat.Lf_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:52:04.297802+00:00
-- url     : https://prove2.me/submissions/16bb79d1-32ee-40f5-9e3c-0ed5870770bb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictLat

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
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
namespace DictLat
theorem _root_.solution (I : AutInst) (p : Submodule (IntAf I.F I.E) (Fin I.n → I.E ⊗[I.F] Af I.F))
    (h : ∀ l ∈ I.L, iv I l ∈ p) : I.Lf ≤ p := by
  show Submodule.span _ _ ≤ p
  rw [Submodule.span_le]
  rintro _ ⟨⟨l, hl⟩, rfl⟩
  exact h l hl
end DictLat
end PIW.AdelClassFin
