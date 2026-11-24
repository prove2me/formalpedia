-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.opApply_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:54:01.312623+00:00
-- url     : https://prove2.me/submissions/119dbeba-af23-49d3-abf4-dae97d855bd3

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
theorem _root_.solution {k j ρ : ℕ} (L : FS k (j + ρ)) (hL : ∀ e ∈ L, ∀ X ∈ e.2, inLie k (j + ρ) X)
    (F : Mat k (j + ρ) → (Wq →L[ℂ] Wp)) (g : Mat k (j + ρ)) :
    opApply (L.map (mkTerm (Wp := Wp) (Wq := Wq) k j ρ)) F g = shape k j ρ F L g := by
  unfold opApply shape
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  try simp only [Function.comp_apply]
  rw [mkTerm_word (hL e he)]
  first
  | rfl
  | simp [mkTerm]
end PI.UnitaryGroupMassFormula.UsCompose
