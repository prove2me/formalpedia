-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.inDD_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:47:19.086045+00:00
-- url     : https://prove2.me/submissions/012437af-63cc-43ee-8f57-52380a0735d1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_mkTerm_word

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution {k j ρ κ o : ℕ} (L : FS k (j + ρ)) (h : Bd k j ρ κ o L) :
    InDD k j ρ o κ (L.map (mkTerm (Wp := Wp) (Wq := Wq) k j ρ)) := by
  intro T hT
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hT
  obtain ⟨hdeg, hlen, hlie⟩ := h e he
  refine ⟨by rw [mkTerm_word hlie]; exact hlen, fun g => eval (vars g) e.1.1, e.1.2.1, e.1.2.2,
    ⟨e.1.1, hdeg, fun g => rfl⟩, fun g => rfl⟩
end PI.UnitaryGroupMassFormula.UsCompose
